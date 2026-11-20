import { WorkletSynthesizer } from "https://esm.sh/spessasynth_lib@4.4.0";

const D = await fetch('./app-data.json').then(r => { if (!r.ok) throw new Error('設定データを読み込めません'); return r.json(); });
const INSTRUMENTS = await fetch('./instruments.json').then(r => { if (!r.ok) throw new Error('楽器一覧を読み込めません'); return r.json(); });
const $ = id => document.getElementById(id);
const el = {
  instrument:$('instrument'), mode:$('mode'), range:$('range'), customRange:$('customRange'), rangeMin:$('rangeMin'), rangeMax:$('rangeMax'),
  ordinaryRange:$('ordinaryRange'), instrumentRange:$('instrumentRange'), melodySettings:$('melodySettings'), melodySelection:$('melodySelection'), melodyStyle:$('melodyStyle'), melodyKeyMode:$('melodyKeyMode'), melodyKey:$('melodyKey'),
  melodyScaleMode:$('melodyScaleMode'), melodyCategory:$('melodyCategory'), melodyScale:$('melodyScale'), melodyCount:$('melodyCount'), melodyRange:$('melodyRange'),
  minutes:$('minutes'), instrumentVolume:$('instrumentVolume'), speechVolume:$('speechVolume'), octaveGap:$('octaveGap'), duration:$('duration'), soundGap:$('soundGap'), questionGap:$('questionGap'), speech:$('speech'), speechModes:$('speechModes'), speed:$('speed'), speedValue:$('speedValue'),
  genre:$('genre'), progressionSettings:$('progressionSettings'), progressionKeyMode:$('progressionKeyMode'), progressionKeyWrap:$('progressionKeyWrap'), progressionKey:$('progressionKey'),
  answer:$('answer'), instrumentLabel:$('instrumentLabel'), status:$('status'), remaining:$('remaining'), soundStatus:$('soundStatus'), loadBar:$('loadBar'), loadPercent:$('loadPercent'), start:$('start'), stop:$('stop')
};

const CATEGORIES = [...new Set(INSTRUMENTS.map(x=>x.category))];
const instrumentById = new Map(INSTRUMENTS.map(x=>[x.id,x]));
let audioContext=null, synth=null, soundLoaded=false, loadingPromise=null;
let runToken=0, playing=false, endAt=0, durationSec=1, soundGapSec=0.5, questionGapSec=1;
let activeTimers=new Set(), activeNotes=[], previousNote=-1, timerTicker=null, wakeLock=null, speechPrimePromise=Promise.resolve();
const pick=a=>a[Math.floor(Math.random()*a.length)];
const sleep=ms=>new Promise(resolve=>{const id=setTimeout(()=>{activeTimers.delete(id);resolve();},Math.max(0,ms));activeTimers.add(id);});
function clearTimers(){for(const id of activeTimers)clearTimeout(id);activeTimers.clear();}
function noteName(midi){return D.NAMES[midi%12]+(Math.floor(midi/12)-1);}
function midiLabel(midi){return noteName(midi);}
function parseNoteText(value){const m=value.trim().toUpperCase().match(/^(C#|DB|D#|EB|E|F#|GB|G#|AB|A#|BB|C|D|F|G|A|B)(-?\d+)$/);if(!m)throw new Error('音名は C2 や F#5 の形式で入力してください');const flat={DB:'C#',EB:'D#',GB:'F#',AB:'G#',BB:'A#'};return (Number(m[2])+1)*12+D.NAMES.indexOf(flat[m[1]]||m[1]);}
function parseKeyText(value){const raw=value.trim().toUpperCase(),n=({DB:'C#',EB:'D#',GB:'F#',AB:'G#',BB:'A#'})[raw]||raw,i=D.NAMES.indexOf(n);if(i<0)throw new Error('キーは C、F#、Bb などで入力してください');return i;}
const POPULAR_PROGRAMS=new Set([0,1,2,4,5,6,11,16,19,24,25,26,27,29,32,33,34,35,40,41,42,43,46,48,49,50,52,53,56,57,60,64,65,66,68,71,73,74,80,81,88,89]);
const SLEEP_PROGRAMS=new Set([0,1,4,5,6,10,11,19,24,25,40,42,46,48,49,50,52,53,71,73,74,88,89,91,92,94,95]);
const POPULAR_IDS=new Set(INSTRUMENTS.filter(x=>x.bank===0&&POPULAR_PROGRAMS.has(x.program)).map(x=>x.id));
const SLEEP_IDS=new Set(INSTRUMENTS.filter(x=>x.bank===0&&SLEEP_PROGRAMS.has(x.program)).map(x=>x.id));
function selectedInstrumentPool(){const v=el.instrument.value;if(v==='custom')return INSTRUMENTS.filter(x=>customInstrumentIds.has(x.id));if(v==='random')return INSTRUMENTS;if(v==='sleep')return INSTRUMENTS.filter(x=>SLEEP_IDS.has(x.id));if(v==='popular')return INSTRUMENTS.filter(x=>POPULAR_IDS.has(x.id));if(v.startsWith('category:'))return INSTRUMENTS.filter(x=>x.category===v.slice(9));return [instrumentById.get(v)].filter(Boolean);}
function chooseInstrument(){let pool=selectedInstrumentPool();if(['1','3'].includes(el.mode.value))pool=pool.filter(chordEligible);if(['1','3'].includes(el.mode.value))pool=pool.filter(x=>{try{const [a,b]=getSelectedRange(x);return b-a>=12;}catch(_){return false;}});if(['0','2'].includes(el.mode.value))pool=pool.filter(x=>{try{getSelectedRange(x);return true;}catch(_){return false;}});if(el.mode.value==='4')pool=pool.filter(x=>{try{getRangeForMelody(x);return true;}catch(_){return false;}});if(!pool.length)throw new Error('選択した条件で使用できる楽器がありません');return pick(pool);}
function getSelectedRange(inst){const [low,high]=inst.range;const selected=Number(el.range.value);if(selected===0)return [low,high];const span=high-low+1,third=Math.floor(span/3);if(selected===1)return [low,low+third-1];if(selected===2)return [low+third,low+third*2-1];if(selected===3)return [low+third*2,high];const a=Math.max(low,parseNoteText(el.rangeMin.value)),b=Math.min(high,parseNoteText(el.rangeMax.value));if(a>b)throw new Error('指定した音域が選択楽器の音域と合っていません');return [a,b];}
function getRangeForMelody(inst){return getSelectedRange(inst);}
function formatRange(range){return `${midiLabel(range[0])} ～ ${midiLabel(range[1])}`;}
function updateInstrumentRange(){const v=el.instrument.value;if(['random','custom','sleep','popular'].includes(v)||v.startsWith('category:'))el.instrumentRange.textContent='出題用音域（目安）：選択された楽器ごとに自動設定';else{const inst=instrumentById.get(v);el.instrumentRange.textContent=inst?`出題用音域（目安）：${formatRange(inst.range)}`:'音域：—';}}
const customInstrumentIds=new Set();
function chordEligible(inst){return inst.supportsChords===true && inst.range[1]-inst.range[0]>=24 && (inst.guitarVoicing || inst.family==='poly');}
function buildCustomInstrumentPicker(){const host=$('customInstrumentList');host.replaceChildren();for(const category of CATEGORIES){const group=document.createElement('fieldset');const legend=document.createElement('legend');legend.textContent=category;group.append(legend);for(const inst of INSTRUMENTS.filter(x=>x.category===category)){const label=document.createElement('label');label.className='instrument-check';const check=document.createElement('input');check.type='checkbox';check.value=inst.id;check.checked=customInstrumentIds.has(inst.id);check.addEventListener('change',()=>{if(check.checked)customInstrumentIds.add(inst.id);else customInstrumentIds.delete(inst.id);updateInstrumentRange();});label.append(check,document.createTextNode(inst.name));group.append(label);}host.append(group);}}
function buildInstrumentOptions(){el.instrument.replaceChildren();el.instrument.add(new Option('全楽器からランダム','random'));el.instrument.add(new Option('睡眠向けの穏やかな楽器からランダム','sleep'));el.instrument.add(new Option('よく使われる楽器からランダム','popular'));el.instrument.add(new Option('自分で選んだ楽器からランダム','custom'));const randomGroup=document.createElement('optgroup');randomGroup.label='カテゴリーからランダム';for(const c of CATEGORIES)randomGroup.append(new Option(`${c}からランダム`,`category:${c}`));el.instrument.append(randomGroup);for(const c of CATEGORIES){const group=document.createElement('optgroup');group.label=c;INSTRUMENTS.filter(x=>x.category===c).forEach(x=>{const opt=new Option(x.name,x.id);opt.dataset.supportsChords=String(chordEligible(x));group.append(opt);});el.instrument.append(group);}buildCustomInstrumentPicker();updateInstrumentRange();}
function buildSpeechSettings(){
  const modes=[['0','単音'],['1','コード'],['2','音程'],['3','コード進行'],['4','メロディ']];
  const parts=[['key','キー・調'],['notes','音名'],['info','音程・コード情報'],['instrument','楽器名'],['inversion','転回形']];
  el.speechModes.replaceChildren();
  for(const [mode,label] of modes){
    const section=document.createElement('section');section.className='speech-mode'+(mode==='0'?'':' hidden');section.dataset.speechMode=mode;
    const h=document.createElement('strong');h.textContent=label+'モード';section.append(h);
    for(const [part,partLabel] of parts){
      if(part==='notes'&&mode==='3')continue;
      if(part==='inversion'&&!['1','3'].includes(mode))continue;
      const row=document.createElement('div');row.className='speech-setting-row';
      const check=document.createElement('input');check.type='checkbox';check.id=`speech-${mode}-${part}`;
      check.checked=(part==='notes'||part==='instrument'||(part==='info'&&['1','2','3'].includes(mode))||(part==='key'&&['3','4'].includes(mode))||(part==='inversion'&&mode==='1'));
      if((part==='key'&&['0','1','2'].includes(mode))||(part==='info'&&['0','4'].includes(mode)))check.disabled=true;
      const txt=document.createElement('label');txt.htmlFor=check.id;txt.textContent=(part==='info'&&mode==='3')?'進行名・ディグリー':partLabel;
      const lang=document.createElement('select');lang.id=`speech-lang-${mode}-${part}`;lang.className='speech-language';
      lang.add(new Option('日本語','ja'));lang.add(new Option('English','en'));lang.value=part==='notes'?'en':'ja';
      if(part==='instrument')lang.classList.add('hidden');
      row.append(check,txt,lang);
      if(part==='notes'){const octave=document.createElement('label');octave.className='octave-setting';const cb=document.createElement('input');cb.type='checkbox';cb.id=`speech-octave-${mode}`;cb.checked=true;octave.append(cb,document.createTextNode('オクターブ番号も読む'));row.append(octave);}
      section.append(row);
    }
    el.speechModes.append(section);
  }
}
function updateSettingsVisibility(){const mode=el.mode.value;el.melodySettings.classList.toggle('hidden',mode!=='4');el.ordinaryRange.classList.remove('hidden');el.customRange.classList.toggle('hidden',el.range.value!=='4');el.progressionSettings.classList.toggle('hidden',mode!=='3');el.speechModes.querySelectorAll('[data-speech-mode]').forEach(x=>x.classList.toggle('hidden',x.dataset.speechMode!==mode));el.progressionKeyWrap.classList.toggle('hidden',el.progressionKeyMode.value!=='1');el.melodyKey.disabled=el.melodyKeyMode.value!=='0';el.melodyScale.disabled=el.melodyScaleMode.value!=='0';el.melodyCategory.disabled=el.melodyScaleMode.value==='1';$('customInstrumentPanel').classList.toggle('hidden',el.instrument.value!=='custom');const chordMode=['1','3'].includes(mode);for(const check of document.querySelectorAll('#customInstrumentList input[type=checkbox]')){const inst=instrumentById.get(check.value);check.disabled=chordMode&&!chordEligible(inst);}for(const opt of el.instrument.querySelectorAll('option[data-supports-chords]'))opt.hidden=chordMode&&opt.dataset.supportsChords!=='true';for(const opt of el.instrument.querySelectorAll('optgroup option')){if(opt.value.startsWith('category:')){const cat=opt.value.slice(9);opt.hidden=chordMode&&!INSTRUMENTS.some(x=>x.category===cat&&chordEligible(x));}}const selected=el.instrument.selectedOptions[0];if(chordMode&&selected?.dataset.supportsChords==='false'){el.instrument.value='random';}updateInstrumentRange();}
function updateMelodyScales(){const category=Object.keys(D.SCALE_CATEGORIES)[Number(el.melodyCategory.value)]||Object.keys(D.SCALE_CATEGORIES)[0],list=D.SCALE_CATEGORIES[category],old=el.melodyScale.value;el.melodyScale.replaceChildren();list.forEach((name,i)=>el.melodyScale.add(new Option(name,String(i))));if(list.includes(old))el.melodyScale.value=String(list.indexOf(old));}
function populateSettings(){D.NAMES.forEach((name,i)=>el.melodyKey.add(new Option(name,String(i))));Object.keys(D.SCALE_CATEGORIES).forEach((name,i)=>el.melodyCategory.add(new Option(name,String(i))));updateMelodyScales();}
function setLoadProgress(percent,message){const p=Math.max(0,Math.min(100,Math.round(percent)));el.loadBar.style.width=p+'%';el.loadPercent.textContent=p+'%';el.soundStatus.textContent=message;}
async function fetchWithProgress(url){
  const response=await fetch(url);if(!response.ok)throw new Error(`SoundFontを読み込めません（${response.status}）`);
  const total=Number(response.headers.get('content-length'))||0;
  if(!response.body){const b=await response.arrayBuffer();setLoadProgress(75,'SoundFontをダウンロードしました');return b;}
  const reader=response.body.getReader(),chunks=[];let loaded=0,lastAt=performance.now(),lastLoaded=0,rate=0;
  while(true){
    const {done,value}=await reader.read();if(done)break;chunks.push(value);loaded+=value.byteLength;
    const now=performance.now(),dt=(now-lastAt)/1000;
    if(dt>=0.35){const instant=(loaded-lastLoaded)/dt;rate=rate?rate*0.7+instant*0.3:instant;lastAt=now;lastLoaded=loaded;}
    const pct=total?Math.min(75,Math.round(loaded/total*75)):Math.min(70,Math.round(loaded/30000000*70));
    const eta=total&&rate>0?Math.ceil((total-loaded)/rate):null;
    const etaText=eta===null?'残り時間を計算中':`残り約${Math.floor(eta/60)}分${String(eta%60).padStart(2,'0')}秒`;
    setLoadProgress(pct,`SoundFontをダウンロード中… ${(loaded/1024/1024).toFixed(1)} MB / ${etaText}`);
  }
  const out=new Uint8Array(loaded);let offset=0;for(const c of chunks){out.set(c,offset);offset+=c.length;}return out.buffer;
}
async function loadSoundBank(){if(loadingPromise)return loadingPromise;loadingPromise=(async()=>{setLoadProgress(1,'音源の読み込みを準備中…');const Ctx=window.AudioContext||window.webkitAudioContext;if(!Ctx)throw new Error('このブラウザはWeb Audio APIに対応していません');audioContext=new Ctx({latencyHint:'interactive'});const workletURL='https://cdn.jsdelivr.net/npm/spessasynth_lib@4.4.0/dist/spessasynth_processor.min.js';setLoadProgress(3,'音源エンジンを準備中…');await audioContext.audioWorklet.addModule(workletURL);synth=new WorkletSynthesizer(audioContext);synth.connect(audioContext.destination);await synth.isReady;const compressed=await fetchWithProgress('./assets/GeneralUser-GS.sf2.gz');setLoadProgress(78,'SoundFontを展開中…');if(!('DecompressionStream'in window))throw new Error('このブラウザはgzip展開に対応していません');const stream=new Blob([compressed]).stream().pipeThrough(new DecompressionStream('gzip'));const bank=await new Response(stream).arrayBuffer();setLoadProgress(86,'261プリセットを含むSoundFontを登録中…');await synth.soundBankManager.addSoundBank(bank,'GeneralUser-GS');try{synth.controllerChange(0,0,0);synth.controllerChange(0,32,0);synth.programChange(0,0);}catch(_){}setLoadProgress(100,'音源：GeneralUser GS 読み込み完了');soundLoaded=true;el.start.disabled=false;setTimeout(()=>document.querySelector('.loading-area')?.classList.add('hidden'),1200);return true;})();return loadingPromise;}
// v10: record audio commands and audio context transitions.
let audioQuestionNumber=0;
const audioEvents=[];
function audioDiagnostic(message){
  const stamp=(performance.now()/1000).toFixed(2);
  audioEvents.push(`${stamp}s ${message}`);
  if(audioEvents.length>12)audioEvents.shift();
  const node=document.getElementById('audioDiagnostic');
  if(node)node.textContent='再生診断：'+audioEvents.slice(-5).join(' | ');
  console.info('[v11 audio]',message);
}
async function ensureAudioRunning(token){
  if(token!==runToken)return false;
  if(audioContext.state!=='running'){
    audioDiagnostic('AudioContext '+audioContext.state+' → resume');
    await audioContext.resume();
  }
  if(token!==runToken)return false;
  if(audioContext.state!=='running'){
    audioDiagnostic('再開後も '+audioContext.state);
    return false;
  }
  return true;
}
// v11: only release notes started by this app. Never send global MIDI CC120/CC123.
// Those commands may suppress later noteOn messages in the AudioWorklet engine.
function selectPreset(inst){if(!synth)throw new Error('音源エンジンが準備できていません');synth.controllerChange(0,0,inst.bank);synth.controllerChange(0,32,0);synth.programChange(0,inst.program);synth.controllerChange(0,7,Math.round(Number(el.instrumentVolume.value)*1.27));}
function noteOn(note){synth.noteOn(0,note,100);activeNotes.push(note);}
function noteOff(note){try{synth.noteOff(0,note);}catch(_){}activeNotes=activeNotes.filter(x=>x!==note);}
function stopAllNotes(){for(const n of [...activeNotes])noteOff(n);activeNotes=[];}
function setDisplayLines(lines,instrument,status,kind='normal'){el.answer.replaceChildren();el.answer.className='answer-'+kind;for(let i=0;i<lines.length;i++){const div=document.createElement('div');div.className=`answer-line answer-line-${i}`;div.textContent=lines[i];el.answer.append(div);}el.instrumentLabel.textContent='楽器：'+(instrument?.name||'—');el.status.textContent=status||'再生中';}
function setProgressionDisplay(keyText,name,chords,active,instrument,status){
 el.answer.replaceChildren();el.answer.className='answer-progression';
 const head=document.createElement('div');head.className='sequence-heading';head.textContent=`${keyText} / ${name}`;el.answer.append(head);
 const row=document.createElement('div');row.className='progression-grid';
 chords.forEach((chord,i)=>{const item=document.createElement('div');item.className='progression-item'+(i===active?' progression-active':'');const name=document.createElement('div');name.className='progression-chord';name.textContent=chordLabel(chord);const degree=document.createElement('div');degree.className='progression-degree';degree.textContent=chord.degree;item.append(name,degree);row.append(item);});
 el.answer.append(row);el.instrumentLabel.textContent='楽器：'+instrument.name;el.status.textContent=status;
}
function setSequenceDisplay(title,notes,active,instrument,status,extra=''){el.answer.replaceChildren();el.answer.className='answer-sequence';const heading=document.createElement('div');heading.className='sequence-heading';heading.textContent=title;el.answer.append(heading);const row=document.createElement('div');row.className='sequence-notes';notes.forEach((n,i)=>{const span=document.createElement('span');span.textContent=noteName(n);span.className=i===active?'active-melody-note':'melody-note';row.append(span);if(i<notes.length-1)row.append(document.createTextNode(' → '));});el.answer.append(row);if(extra){const sub=document.createElement('div');sub.className='sequence-sub';sub.textContent=extra;el.answer.append(sub);}el.instrumentLabel.textContent='楽器：'+instrument.name;el.status.textContent=status;}
function setChordDisplay(chord,instrument,active=-1,status='コード再生中'){el.answer.replaceChildren();el.answer.className='answer-chord';const head=document.createElement('div');head.className='sequence-heading';head.textContent=chordLabel(chord)+' / '+(D.INVERSION_NAMES[chord.inversion]||'基本形');el.answer.append(head);const row=document.createElement('div');row.className='sequence-notes';chord.notes.forEach((n,i)=>{const span=document.createElement('span');span.textContent=noteName(n);span.className=(active===-1||active===i)?'active-melody-note':'melody-note';row.append(span);if(i<chord.notes.length-1)row.append(document.createTextNode(' - '));});el.answer.append(row);if(chord.frets){const f=document.createElement('div');f.className='sequence-sub';f.textContent='フォーム（6弦→1弦）：'+chord.frets.map(x=>x===null?'×':x).join('-');el.answer.append(f);}el.instrumentLabel.textContent='楽器：'+instrument.name;el.status.textContent=status;}
function speechEnabled(mode,part){return el.speech.value==='on'&&!!$(`speech-${mode}-${part}`)?.checked;}
function speechLang(mode,part){return $(`speech-lang-${mode}-${part}`)?.value==='en'?'en-US':'ja-JP';}
function pitchText(pitch,lang){if(lang==='en-US')return D.ENGLISH_SPEECH_NAMES[pitch];return D.JAPANESE_SPEECH_NAMES[pitch];}
async function speakPitch(pitch,lang){if(lang==='en-US'&&[4,5,9].includes(pitch)){await speak(({4:'イー',5:'エフ',9:'エー'})[pitch],'ja-JP');}else await speak(pitchText(pitch,lang),lang);}
function noteSpeech(note,mode){const lang=speechLang(mode,'notes'),pitch=note%12,oct=Math.floor(note/12)-1;return {text:pitchText(pitch,lang),lang,octave:$(`speech-octave-${mode}`)?.checked?String(oct):null};}
// v9: one utterance at a time; never let a stalled iOS speech event block the next question.
let activeSpeech=null;
let speechFailures=0;
let speechRequestNumber=0;
function recoverAfterSpeech(){
  if(!playing||!audioContext)return;
  const state=audioContext.state;
  audioDiagnostic('読み上げ後 AudioContext='+state);
  if(state!=='running')audioContext.resume().then(()=>audioDiagnostic('再開結果 '+audioContext.state)).catch(e=>audioDiagnostic('再開失敗 '+e.message));
}
function speechDiagnostic(message){
  console.info('[v9 speech]',message);
  const target=document.getElementById('speechDiagnostic');
  if(target)target.textContent='読み上げ診断：'+message;
}
function cancelActiveSpeech(){
  const current=activeSpeech;
  if(current)current.finish('停止によりキャンセル');
  try{window.speechSynthesis?.cancel();}catch(_){}
}
function speak(text,lang='ja-JP'){
  if(el.speech.value!=='on'||!text)return Promise.resolve();
  if(!('speechSynthesis'in window)||!('SpeechSynthesisUtterance'in window)){
    speechDiagnostic('このブラウザでは読み上げを利用できません');
    return Promise.resolve();
  }
  return new Promise(resolve=>{
    // A previous utterance that failed to finish must not overlap the next one.
    if(activeSpeech)cancelActiveSpeech();
    const synth=window.speechSynthesis;
    const request=++speechRequestNumber;
    const requestedAt=performance.now();
    speechDiagnostic(`音声${request} 発行 / AudioContext=${audioContext?.state}`);
    const u=new SpeechSynthesisUtterance(String(text));
    u.lang=lang;u.rate=Number(el.speed.value);u.volume=Number(el.speechVolume.value)/100;
    let finished=false,started=false,startTimer=null,endTimer=null;
    const state={finish:(reason)=>{
      if(finished)return;
      finished=true;
      clearTimeout(startTimer);clearTimeout(endTimer);
      u.onstart=u.onend=u.onerror=null;
      if(activeSpeech===state)activeSpeech=null;
      const elapsed=((performance.now()-requestedAt)/1000).toFixed(2);
      audioDiagnostic(`音声${request} ${reason} ${elapsed}秒 / AudioContext=${audioContext?.state}`);
      recoverAfterSpeech();
      if(reason!=='完了'&&reason!=='停止によりキャンセル'){
        speechFailures++;speechDiagnostic(`${reason}（累計${speechFailures}回）`);
      }else if(reason==='完了')speechDiagnostic(`音声${request} 正常終了（合計${elapsed}秒）`);
      resolve();
    }};
    activeSpeech=state;
    u.onstart=()=>{
      if(finished)return;
      started=true;clearTimeout(startTimer);
      speechDiagnostic(`音声${request} 開始待ち${((performance.now()-requestedAt)/1000).toFixed(2)}秒 / AudioContext=${audioContext?.state}`);
      // Fail safe only: actual completion is governed by onend.
      const limit=Math.min(12000,Math.max(4000,1800+String(text).length*250/Math.max(.4,u.rate)));
      endTimer=setTimeout(()=>{
        if(finished)return;
        try{synth.cancel();}catch(_){}
        state.finish('終了通知が届かずタイムアウト');
      },limit);
    };
    u.onend=()=>state.finish('完了');
    u.onerror=e=>state.finish('読み上げエラー：'+(e.error||'不明'));
    startTimer=setTimeout(()=>{
      if(finished||started)return;
      try{synth.cancel();}catch(_){}
      state.finish('開始通知が届かずタイムアウト');
    },3000);
    try{
      if(synth.paused)synth.resume();
      synth.speak(u);
      if(synth.paused)synth.resume();
    }catch(e){state.finish('開始例外：'+e.message);}
  });
}
async function speakPart(mode,part,text){if(speechEnabled(mode,part))await speak(text,speechLang(mode,part));}
async function speakInstrument(inst,mode){const ja=inst.nameJa||inst.name;const isJapanese=/[ぁ-んァ-ヶ一-龠]/.test(ja||'');const name=isJapanese?ja:(inst.presetName||inst.name||ja);await speakPart(mode,'instrument',name);}
async function speakNotes(notes,mode){if(!speechEnabled(mode,'notes'))return;for(const n of notes){const spec=noteSpeech(n,mode);const gap=Number(el.octaveGap.value);if(spec.octave!==null&&gap===0){ // One utterance avoids an artificial pause between pitch and octave.
 const pitch=n%12;const combined=spec.lang==='en-US'?`${D.ENGLISH_SPEECH_NAMES[pitch]} ${D.OCTAVE_ENGLISH?.[spec.octave]||spec.octave}`:`${spec.text} ${D.OCTAVE_ENGLISH?.[spec.octave]||spec.octave}`;
 await speak(combined,spec.lang);
 }else{await speakPitch(n%12,spec.lang);if(spec.octave!==null){await sleep(gap*1000);await speak(spec.octave,'en-US');}}}}

function intervalName(semitones,lang){const ja=(D.INTERVALS[String(semitones)]||`${semitones}半音`).replace(/^短/,'たん').replace(/^長/,'ちょう').replace(/^完全/,'かんぜん').replace(/^増/,'ぞう').replace(/^減/,'げん').replace(/度/g,'ど').replace(/2/g,'に').replace(/3/g,'さん').replace(/4/g,'よん').replace(/5/g,'ご').replace(/6/g,'ろく').replace(/7/g,'なな').replace(/8/g,'はち');const en={1:'minor second',2:'major second',3:'minor third',4:'major third',5:'perfect fourth',6:'tritone',7:'perfect fifth',8:'minor sixth',9:'major sixth',10:'minor seventh',11:'major seventh',12:'perfect octave'}[semitones]||`${semitones} semitones`;return lang==='en-US'?en:ja;}
function chordLabel(chord){return D.NAMES[chord.root%12]+(D.CHORD_DISPLAY_NAMES[chord.name]||chord.name);}
function chordEnglish(chord){const quality={Major:'major',Minor:'minor',aug:'augmented',sus4:'sus four','7th':'seven',Major7:'major seven',Minor7:'minor seven',dim:'diminished',HalfDim7:'minor seven flat five'}[chord.name]||chord.name;return `${pitchText(chord.root,'en-US')} ${quality}`;}
function chordJapanese(chord) {
    const quality = {
        Major: "メジャー",
        Minor: "マイナー",
        aug: "オーギュメント",
        sus4: "サスフォー",
        "7th": "セブンス",
        Major7: "メジャーセブンス",
        Minor7: "マイナーセブンス",
        dim: "ディミニッシュ",
        HalfDim7: "ハーフディミニッシュセブンス"
    }[chord.name] || chord.name;

    return `${D.JAPANESE_SPEECH_NAMES[chord.root]} ${quality}`;
}
function inversionName(index){return D.INVERSION_NAMES[index]||'';}
function inversionSpeech(index,mode){const lang=speechLang(mode,'inversion');const en=D.INVERSION_SPEECH_EN?.[index]||['root position','first inversion','second inversion','third inversion'][index]||'';return lang==='en-US'?en:(D.INVERSION_SPEECH_JA?.[index]||D.INVERSION_NAMES[index]||'きほんけい');}
function genericChordNotes(root,intervals,inst,inversion=0){const [low,high]=getSelectedRange(inst),pcs=intervals.map(x=>(root+x)%12),candidates=[];for(let base=low;base<=high;base++){if(base%12!==pcs[inversion%pcs.length])continue;const notes=[base];for(let j=1;j<intervals.length;j++){const pc=pcs[(inversion+j)%pcs.length];let n=notes.at(-1)+1;while(n<=high&&n%12!==pc)n++;if(n>high)break;notes.push(n);}if(notes.length===intervals.length)candidates.push(notes);}if(!candidates.length)throw new Error(`${inst.name}の音域内にコードを配置できません`);return pick(candidates);}
function guitarVoicings(root,intervals,inversion,inst,maxFret=12){const [low,high]=getSelectedRange(inst),pcs=new Set(intervals.map(x=>(root+x)%12)),bass=(root+intervals[inversion])%12,opts=D.GUITAR_OPEN_STRINGS.map(open=>{const a=[null];for(let f=0;f<=maxFret;f++){const n=open+f;if(n>=low&&n<=high&&pcs.has(n%12))a.push(f);}return a;}),results=[];function visit(i,frets){if(i<opts.length){for(const f of opts[i])visit(i+1,[...frets,f]);return;}const notes=frets.map((f,j)=>f===null?null:D.GUITAR_OPEN_STRINGS[j]+f).filter(x=>x!==null);if(notes.length<4||!pcs.size||notes[0]%12!==bass||notes.some((n,j)=>j&&n<notes[j-1]))return;if([...pcs].some(pc=>!notes.some(n=>n%12===pc)))return;const pressed=frets.filter(f=>f!==null&&f>0);if(pressed.length&&(Math.max(...pressed)-Math.min(...pressed)>4||new Set(pressed).size>4))return;results.push({frets,notes});}visit(0,[]);return results;}
function generateGuitarChord(inst){for(let i=0;i<100;i++){const name=pick(Object.keys(D.CHORD_TYPES)),intervals=D.CHORD_TYPES[name],inv=Math.floor(Math.random()*intervals.length),root=Math.floor(Math.random()*12),list=guitarVoicings(root,intervals,inv,inst,12);if(list.length){const v=pick(list);return {name,root,inversion:inv,notes:v.notes,frets:v.frets};}}const name='Major',root=Math.floor(Math.random()*12),intervals=D.CHORD_TYPES[name];return {name,root,inversion:0,notes:genericChordNotes(root,intervals,inst,0),frets:null};}
function generateChord(inst){if(inst.guitarVoicing)return generateGuitarChord(inst);for(let i=0;i<80;i++){const name=pick(Object.keys(D.CHORD_TYPES)),intervals=D.CHORD_TYPES[name],inversion=Math.floor(Math.random()*intervals.length),root=Math.floor(Math.random()*12);try{return {name,root,inversion,notes:genericChordNotes(root,intervals,inst,inversion),frets:null};}catch(_){}}const name='Major',root=Math.floor(Math.random()*12);return {name,root,inversion:0,notes:genericChordNotes(root,D.CHORD_TYPES[name],inst,0),frets:null};}
function generateSingle(){const inst=chooseInstrument(),[low,high]=getSelectedRange(inst);let list=Array.from({length:high-low+1},(_,i)=>low+i);if(list.length>1&&list.includes(previousNote))list=list.filter(x=>x!==previousNote);const note=pick(list);previousNote=note;return {inst,note};}
function generateInterval(){const inst=chooseInstrument(),[low,high]=getSelectedRange(inst),semitones=Object.keys(D.INTERVALS).map(Number).filter(n=>high-low>=n);if(!semitones.length)throw new Error('選択した音域が狭すぎて音程を生成できません');const gap=pick(semitones),direction=pick(['上昇','下降']);const first=direction==='上昇'?Math.floor(Math.random()*(high-gap-low+1))+low:Math.floor(Math.random()*(high-(low+gap)+1))+low+gap;return {inst,first,second:direction==='上昇'?first+gap:first-gap,gap,direction};}
function generateMelody(){
  const inst=chooseInstrument(),[low,high]=getRangeForMelody(inst),count=Number(el.melodyCount.value)===0?3+Math.floor(Math.random()*6):Number(el.melodyCount.value);
  const key=el.melodyKeyMode.value==='1'?Math.floor(Math.random()*12):Number(el.melodyKey.value);
  const all=Object.values(D.SCALE_CATEGORIES).flat(),categoryScales=D.SCALE_CATEGORIES[Object.keys(D.SCALE_CATEGORIES)[Number(el.melodyCategory.value)]],scaleName=el.melodyScaleMode.value==='1'?pick(all):el.melodyScaleMode.value==='2'?pick(categoryScales):categoryScales[Number(el.melodyScale.value)];
  let candidates=Array.from({length:high-low+1},(_,i)=>low+i);
  const scaleSet=new Set(D.SCALES[scaleName].map(x=>(key+x)%12));
  if(el.melodySelection.value==='1'||el.melodyStyle?.value==='natural')candidates=candidates.filter(n=>scaleSet.has(n%12));
  if(!candidates.length)throw new Error('選択した条件では音を生成できません');
  let notes=[];
  if(el.melodyStyle?.value==='natural'){
    const center=(low+high)/2;
    let previous=candidates.reduce((a,b)=>Math.abs(b-center)<Math.abs(a-center)?b:a,candidates[0]);
    for(let i=0;i<count;i++){
      let choices=candidates.filter(n=>Math.abs(n-previous)<=4&&n!==previous);
      if(i===0)choices=candidates.filter(n=>Math.abs(n-previous)<=7);
      if(i===count-1){const resolved=candidates.filter(n=>[0,7].includes((n-key+120)%12));if(resolved.length)choices=resolved;}
      if(!choices.length)choices=candidates;
      const weights=choices.map(n=>1/(1+Math.abs(n-previous))*(i===count-1&&((n-key+120)%12===0)?2.5:1));
      let r=Math.random()*weights.reduce((a,b)=>a+b,0),chosen=choices[0];
      for(let j=0;j<choices.length;j++){r-=weights[j];if(r<=0){chosen=choices[j];break;}}
      notes.push(chosen);previous=chosen;
    }
  }else notes=Array.from({length:count},()=>pick(candidates));
  return {inst,notes,key,scaleName};
}
function generateProgressionChord(data,inst,key){const [offset,type,degree,spoken]=data,root=(key+offset)%12,intervals=D.CHORD_TYPES[type];if(inst.guitarVoicing){const list=guitarVoicings(root,intervals,0,inst,12);if(list.length){const v=pick(list);return {name:type,root,inversion:0,notes:v.notes,frets:v.frets,degree,spoken};}}return {name:type,root,inversion:0,notes:genericChordNotes(root,intervals,inst,0),frets:null,degree,spoken};}
async function playSingleFor(inst,note,ms,token){
  if(token!==runToken)return;
  const question=++audioQuestionNumber;
  audioDiagnostic(`問${question} 準備 ${noteName(note)} (${audioContext.state})`);
  if(!await ensureAudioRunning(token))return;
  stopAllNotes();
  selectPreset(inst);
  if(token!==runToken)return;
  audioDiagnostic(`問${question} noteOn ${noteName(note)} (${audioContext.state}) / 発音管理=${activeNotes.length}`);
  noteOn(note);
  try{await sleep(ms);}
  finally{
    noteOff(note);
    audioDiagnostic(`問${question} noteOff (${audioContext.state}) / 発音管理=${activeNotes.length}`);
  }
}
async function playChordFor(inst,chord,ms,token,mode,displayTitle){if(token!==runToken)return;if(!await ensureAudioRunning(token))return;stopAllNotes();selectPreset(inst);const notes=chord.notes;if((inst.family==='mono'||inst.guitarVoicing)&&!chord.frets){const each=Math.max(140,Math.min(320,ms/Math.max(1,notes.length)));for(let i=0;i<notes.length;i++){if(token!==runToken)return;if(mode!=='3')setChordDisplay(chord,inst,i,displayTitle||'アルペジオ再生中');noteOn(notes[i]);await sleep(each);noteOff(notes[i]);if(i<notes.length-1)await sleep(45);}return;}if(chord.frets){for(let i=0;i<notes.length;i++){if(token!==runToken)return;if(mode!=='3')setChordDisplay(chord,inst,i,'コードをストローク中');noteOn(notes[i]);await sleep(28);}await sleep(ms);if(token===runToken)stopAllNotes();return;}for(const n of notes)noteOn(n);await sleep(ms);if(token===runToken)stopAllNotes();}
function requestWakeLock(){if(!('wakeLock'in navigator))return;navigator.wakeLock.request('screen').then(x=>{wakeLock=x;x.addEventListener('release',()=>wakeLock=null);}).catch(()=>{});}
async function releaseWakeLock(){if(wakeLock){try{await wakeLock.release();}catch(_){}wakeLock=null;}}
function configureIOSAudio(){try{if(navigator.audioSession)navigator.audioSession.type='playback';}catch(_){}}
// v7 experimental background-audio controls. iOS may still suspend JS timers or speech synthesis.
function updateMediaSession(active){
  if(!('mediaSession' in navigator))return;
  try{
    navigator.mediaSession.metadata=new MediaMetadata({title:'音感トレーニング',artist:'Random Piano & Guitar',album:'バックグラウンド再生 実験版 v11'});
    navigator.mediaSession.playbackState=active?'playing':'paused';
    navigator.mediaSession.setActionHandler('play',()=>{if(!playing)startSession();else audioContext?.resume().catch(()=>{});});
    navigator.mediaSession.setActionHandler('pause',()=>{console.info('[v8] Media Session pause event (no automatic session stop)');});
    navigator.mediaSession.setActionHandler('stop',()=>{console.info('[v8] Media Session stop event (no automatic session stop)');});
  }catch(e){console.warn('Media Session unavailable',e);}
}
function restoreAudioIfNeeded(){
  if(!playing)return;
  configureIOSAudio();
  if(audioContext?.state==='suspended')audioContext.resume().catch(()=>{});
  updateMediaSession(true);
}

function primeSpeech(){speechDiagnostic('初期化開始 / AudioContext='+audioContext?.state);if(!('speechSynthesis'in window))return;try{const s=window.speechSynthesis,u=new SpeechSynthesisUtterance('あ');u.lang='ja-JP';u.volume=0.01;s.cancel();s.speak(u);speechPrimePromise=new Promise(resolve=>{let done=false;const finish=()=>{if(done)return;done=true;clearTimeout(t);resolve();};u.onend=finish;u.onerror=finish;const t=setTimeout(finish,1800);});}catch(_){speechPrimePromise=Promise.resolve();}}
function formatRemaining(ms){const s=Math.max(0,Math.ceil(ms/1000));return `${String(Math.floor(s/60)).padStart(2,'0')}:${String(s%60).padStart(2,'0')}`;}
function updateTimer(){const left=endAt-Date.now();el.remaining.textContent='残り時間：'+formatRemaining(left);if(left<=0&&playing)stopSession('時間終了');}
async function runSingle(token){const q=generateSingle();setDisplayLines([noteName(q.note)],q.inst,'単音を再生中');await playSingleFor(q.inst,q.note,durationSec*1000,token);if(token!==runToken)return;await speakNotes([q.note],'0');await speakInstrument(q.inst,'0');if(token===runToken)await sleep(questionGapSec*1000);}
async function runChord(token){let inst=null,chord=null;for(const candidate of selectedInstrumentPool().filter(x=>{try{const [a,b]=getSelectedRange(x);return chordEligible(x)&&b-a>=12;}catch(_){return false;}}).sort(()=>Math.random()-0.5)){try{chord=generateChord(candidate);inst=candidate;break;}catch(_){}}if(!inst)throw new Error('コードを生成できる楽器がありません');setChordDisplay(chord,inst,-1,'コード再生中');await playChordFor(inst,chord,durationSec*1000,token,'1');if(token!==runToken)return;const info=speechLang('1','info')==='en-US'?chordEnglish(chord):chordJapanese(chord);await speakPart('1','info',info);if(chord.inversion>0&&speechEnabled('1','inversion'))await speak(inversionSpeech(chord.inversion,'1'),speechLang('1','inversion'));await speakNotes(chord.notes,'1');await speakInstrument(inst,'1');if(token===runToken)await sleep(questionGapSec*1000);}
async function runInterval(token){const q=generateInterval(),notes=[q.first,q.second],lang=speechLang('2','info');for(let i=0;i<2;i++){setSequenceDisplay('音程',notes,i,q.inst,`音程再生中（${i+1}音目）`);await playSingleFor(q.inst,notes[i],durationSec*1000,token);if(token!==runToken)return;if(i===0)await sleep(soundGapSec*1000);}if(token!==runToken)return;const intervalJa=D.INTERVALS[String(q.gap)]||`${q.gap}半音`;const intervalEn=intervalName(q.gap,'en-US');setSequenceDisplay(`${intervalJa}（${q.direction}）`,notes,1,q.inst,'音程の問題が終了');const info=intervalName(q.gap,lang)+(lang==='en-US'?(q.direction==='上昇'?' ascending':' descending'):(q.direction==='上昇'?'上昇':'下降'));await speakPart('2','info',info);await speakNotes(notes,'2');await speakInstrument(q.inst,'2');if(token===runToken)await sleep(questionGapSec*1000);}
async function runMelody(token){const m=generateMelody();for(let i=0;i<m.notes.length;i++){setSequenceDisplay(`${D.NAMES[m.key]} / ${m.scaleName}`,m.notes,i,m.inst,`メロディ再生中 ${i+1}/${m.notes.length}`);await playSingleFor(m.inst,m.notes[i],durationSec*1000,token);if(token!==runToken)return;if(i<m.notes.length-1)await sleep(soundGapSec*1000);}if(token!==runToken)return;const keyLang=speechLang('4','key'),keyText=pitchText(m.key,keyLang),scale=(keyLang==='en-US'?D.SCALE_ENGLISH_NAMES:D.SCALE_JAPANESE_NAMES)[m.scaleName]||m.scaleName;await speakPart('4','key',keyText+' '+scale);await speakNotes(m.notes,'4');await speakInstrument(m.inst,'4');if(token===runToken)await sleep(questionGapSec*1000);}
async function runProgression(token){
  const genre=el.genre.value,choices=D.PROGRESSIONS.filter(p=>genre==='すべて'||p.genre===genre);
  if(!choices.length)throw new Error('選択されたジャンルに進行がありません');
  const progression=pick(choices),key=el.progressionKeyMode.value==='0'?Math.floor(Math.random()*12):parseKeyText(el.progressionKey.value);
  const candidates=selectedInstrumentPool().filter(x=>{try{const [a,b]=getSelectedRange(x);return chordEligible(x)&&b-a>=12;}catch(_){return false;}}).sort(()=>Math.random()-0.5);let inst=null,chords=null;for(const candidate of candidates){try{const generated=progression.chords.map(data=>generateProgressionChord(data,candidate,key));inst=candidate;chords=generated;break;}catch(_){}}if(!inst)throw new Error('このコード進行を演奏できる楽器が選択されていません');
  const keyLabel=`${D.NAMES[key]} ${progression.mode==='major'?'メジャー':'マイナー'}`;
  for(let i=0;i<chords.length;i++){
    if(token!==runToken)return;
    setProgressionDisplay(keyLabel,progression.name,chords,i,inst,`コード進行 ${i+1}/${chords.length}`);
    await playChordFor(inst,chords[i],durationSec*1000,token,'3',`コード ${i+1}`);
    if(token!==runToken)return;
    if(i<chords.length-1)await sleep(soundGapSec*1000);
  }
  if(token!==runToken)return;
  const keyLang=speechLang('3','key'),keyText=pitchText(key,keyLang)+(progression.mode==='major'?(keyLang==='en-US'?' major':'メジャー'):(keyLang==='en-US'?' minor':'マイナー'));
  await speakPart('3','key',keyText);
  if(speechEnabled('3','info')){
    const lang=speechLang('3','info');
    if(lang==='ja-JP')await speak(D.PROGRESSION_READINGS[progression.name]||progression.name,'ja-JP');
    for(const chord of chords){
      const degree=chord.degree.replace(/[♭♯]/g,'').replace(/[^IViv]/g,'').toUpperCase();
      const number={I:1,II:2,III:3,IV:4,V:5,VI:6,VII:7}[degree];
      const prefix=chord.degree.startsWith('♭')?(lang==='en-US'?'flat ':'フラット'):chord.degree.includes('♯')?(lang==='en-US'?'sharp ':'シャープ'):'';
      const numeral=lang==='en-US'?(['','one','two','three','four','five','six','seven'][number]||chord.degree):(['','いち','に','さん','よん','ご','ろく','なな'][number]||chord.spoken||chord.degree);
      const quality=chord.degree.includes('m7♭5')?(lang==='en-US'?' minor seven flat five':'マイナーセブンフラットファイブ'):chord.degree.includes('maj7')?(lang==='en-US'?' major seven':'メジャーセブン'):chord.degree.includes('m7')?(lang==='en-US'?' minor seven':'マイナーセブン'):chord.degree.includes('7')?(lang==='en-US'?' seven':'セブン'):(chord.degree.endsWith('m')||(/^[iv]+$/.test(chord.degree)))?(lang==='en-US'?' minor':'マイナー'):'';
      const text=prefix+numeral+quality;
      await speak(text,lang);
    }
  }
  await speakInstrument(inst,'3');
  if(token===runToken)await sleep(questionGapSec*1000);
}
async function sessionLoop(token){while(playing&&token===runToken&&Date.now()<endAt){switch(el.mode.value){case'0':await runSingle(token);break;case'1':await runChord(token);break;case'2':await runInterval(token);break;case'3':await runProgression(token);break;case'4':await runMelody(token);break;}}if(token===runToken&&playing)stopSession('時間終了');}
function validateSettings(){const minutes=Number(el.minutes.value),duration=Number(el.duration.value),soundGap=Number(el.soundGap.value),questionGap=Number(el.questionGap.value);if(!Number.isFinite(minutes)||minutes<0.1||minutes>600)throw new Error('再生時間は0.1〜600分で指定してください');if(!Number.isFinite(duration)||duration<=0)throw new Error('音の長さは0秒より大きくしてください');if(!Number.isFinite(Number(el.octaveGap.value))||Number(el.octaveGap.value)<0)throw new Error('音名とオクターブ番号の間隔は0秒以上にしてください');if(!Number.isFinite(soundGap)||soundGap<0||!Number.isFinite(questionGap)||questionGap<0)throw new Error('間隔は0秒以上で指定してください');if(!selectedInstrumentPool().some(x=>{try{getSelectedRange(x);return true;}catch(_){return false;}}))throw new Error('選択した音域に対応する楽器がありません');if(['1','3'].includes(el.mode.value)&&!selectedInstrumentPool().some(x=>{try{const [a,b]=getSelectedRange(x);return chordEligible(x)&&b-a>=12;}catch(_){return false;}}))throw new Error('コード演奏に対応した楽器を選択してください');if(el.mode.value==='4'&&!selectedInstrumentPool().some(x=>{try{getRangeForMelody(x);return true;}catch(_){return false;}}))throw new Error('選択した楽器とメロディ音域が一致しません');if(el.mode.value==='3'&&el.progressionKeyMode.value==='1')parseKeyText(el.progressionKey.value);durationSec=duration;soundGapSec=soundGap;questionGapSec=questionGap;return minutes;}
async function startSession(){if(playing||!soundLoaded)return;configureIOSAudio();if(el.speech.value==='on')primeSpeech();let minutes;try{minutes=validateSettings();}catch(e){el.status.textContent=e.message;return;}requestWakeLock();el.start.disabled=true;el.stop.disabled=true;try{await audioContext.resume();if(el.speech.value==='on')await speechPrimePromise;playing=true;audioQuestionNumber=0;audioEvents.length=0;updateMediaSession(true);runToken++;const token=runToken;endAt=Date.now()+minutes*60000;previousNote=-1;el.stop.disabled=false;el.status.textContent='トレーニング中';timerTicker=setInterval(updateTimer,250);updateTimer();sessionLoop(token).catch(e=>{if(token===runToken)stopSession('再生エラー：'+e.message);});}catch(e){el.status.textContent='再生準備エラー：'+e.message;el.start.disabled=false;el.stop.disabled=true;releaseWakeLock();}}
function stopSession(reason='停止しました'){if(!playing&&el.start.disabled===false)return;playing=false;updateMediaSession(false);runToken++;clearTimers();releaseWakeLock();if(timerTicker){clearInterval(timerTicker);timerTicker=null;}stopAllNotes();cancelActiveSpeech();try{audioContext?.suspend();}catch(_){}el.start.disabled=!soundLoaded;el.stop.disabled=true;el.status.textContent=reason;el.remaining.textContent='残り時間：00:00';if(reason==='時間終了')el.answer.textContent='終了';}

el.instrument.addEventListener('change',()=>{updateSettingsVisibility();updateInstrumentRange();});el.mode.addEventListener('change',updateSettingsVisibility);el.range.addEventListener('change',updateSettingsVisibility);el.melodyKeyMode.addEventListener('change',updateSettingsVisibility);el.melodyScaleMode.addEventListener('change',updateSettingsVisibility);el.melodyCategory.addEventListener('change',updateMelodyScales);el.progressionKeyMode.addEventListener('change',updateSettingsVisibility);for(const [id,output] of [['instrumentVolume','instrumentVolumeValue'],['speechVolume','speechVolumeValue']])el[id].addEventListener('input',()=>$(output).textContent=el[id].value+'%');el.speed.addEventListener('input',()=>el.speedValue.textContent=Number(el.speed.value).toFixed(1));el.start.addEventListener('click',startSession);el.stop.addEventListener('click',()=>stopSession('停止しました'));
document.addEventListener('visibilitychange',()=>{if(document.visibilityState==='visible'&&playing){restoreAudioIfNeeded();requestWakeLock();}});
window.addEventListener('pageshow',()=>{if(playing)restoreAudioIfNeeded();});
// Do not stop on pagehide: iOS may fire it while switching apps or locking the screen.
// A real navigation/unload still ends the browser document and cannot be kept alive by JavaScript.


buildInstrumentOptions();buildSpeechSettings();populateSettings();updateSettingsVisibility();el.start.disabled=true;el.speedValue.textContent=Number(el.speed.value).toFixed(1);setLoadProgress(0,'音源を読み込んでいます…');loadSoundBank().catch(err=>{setLoadProgress(0,'音源読み込みエラー：'+err.message);el.status.textContent='音源読み込みエラー：'+err.message;el.start.disabled=true;});
