import { WorkletSynthesizer } from "https://esm.sh/spessasynth_lib@4.4.0";

const D = await fetch("./app-data.json").then(r => {
  if (!r.ok) throw new Error("設定データを読み込めませんでした");
  return r.json();
});
const $ = id => document.getElementById(id);
const el = {
  instrument:$('instrument'), mode:$('mode'), range:$('range'), customRange:$('customRange'),
  rangeMin:$('rangeMin'), rangeMax:$('rangeMax'), ordinaryRange:$('ordinaryRange'),
  melodySettings:$('melodySettings'), melodySelection:$('melodySelection'), melodyKeyMode:$('melodyKeyMode'),
  melodyKey:$('melodyKey'), melodyScaleMode:$('melodyScaleMode'), melodyCategory:$('melodyCategory'),
  melodyScale:$('melodyScale'), melodyCount:$('melodyCount'), melodyRange:$('melodyRange'),
  minutes:$('minutes'), duration:$('duration'), interval:$('interval'), speech:$('speech'),
  instrumentSpeech:$('instrumentSpeech'), singleNoteSpeech:$('singleNoteSpeech'), chordSpeech:$('chordSpeech'),
  intervalSpeech:$('intervalSpeech'), progressionSpeech:$('progressionSpeech'), melodyKeySpeech:$('melodyKeySpeech'),
  melodyNotesSpeech:$('melodyNotesSpeech'), melodyScaleSpeech:$('melodyScaleSpeech'),
  nameType:$('nameType'), octave:$('octave'), speed:$('speed'), speedValue:$('speedValue'),
  genre:$('genre'), progressionSettings:$('progressionSettings'), progressionKeyMode:$('progressionKeyMode'), progressionKeyWrap:$('progressionKeyWrap'),
  progressionKey:$('progressionKey'), answer:$('answer'), instrumentLabel:$('instrumentLabel'),
  status:$('status'), remaining:$('remaining'), soundStatus:$('soundStatus'), start:$('start'), stop:$('stop')
};

const INSTRUMENTS = ['ナイロン弦','スチール弦'];
const SOUND_FILES = {'ナイロン弦':'./assets/Nylon.sf2.gz','スチール弦':'./assets/Steel.sf2.gz'};
const instrumentNames = {'ナイロン弦':'ナイロンギター','スチール弦':'スチールギター'};
let audioContext = null;
let workletReady = false;
const synths = new Map();
let runToken = 0;
let playing = false;
let endAt = 0;
let durationSec = 1;
let intervalSec = 1;
let activeTimers = new Set();
let activeNotes = [];
let previousNote = -1;
let timerTicker = null;
let speechPrimed = false;
let speechPrimePromise = Promise.resolve();
let wakeLock = null;

const pick = a => a[Math.floor(Math.random()*a.length)];
const sleep = ms => new Promise(resolve => {
  const id = setTimeout(() => { activeTimers.delete(id); resolve(); }, Math.max(0,ms));
  activeTimers.add(id);
});
function clearTimers(){ for(const id of activeTimers) clearTimeout(id); activeTimers.clear(); }
function noteName(midi){ return D.NAMES[midi%12] + (Math.floor(midi/12)-1); }
function parseNoteText(value){
  const m = value.trim().toUpperCase().match(/^(C#|DB|D#|EB|E|F#|GB|G#|AB|A#|BB|C|D|F|G|A|B)(-?\d+)$/);
  if(!m) throw new Error('音名は C2 や F#5 の形式で入力してください');
  const flat = {DB:'C#',EB:'D#',GB:'F#',AB:'G#',BB:'A#'};
  const n = flat[m[1]] || m[1];
  return (Number(m[2])+1)*12 + D.NAMES.indexOf(n);
}
function parseKeyText(value){
  const raw=value.trim().toUpperCase();
  const n=({DB:'C#',EB:'D#',GB:'F#',AB:'G#',BB:'A#'})[raw] || raw;
  const i=D.NAMES.indexOf(n);
  if(i<0) throw new Error('キーは C、F#、Bb などで入力してください');
  return i;
}
function selectedInstrument(){return el.instrument.value;}
function chooseInstrument(){const v=selectedInstrument();return v==='ランダム'?pick(INSTRUMENTS):v;}
function getSelectedRange(instrument){
  const [low,high]=D.RANGES[instrument];
  const selected=Number(el.range.value);
  if(selected===0)return [low,high];
  if(selected===1)return [low,low+Math.floor((high-low)/3)];
  if(selected===2)return [low+Math.floor((high-low)/3)+1,low+2*Math.floor((high-low)/3)];
  if(selected===3)return [low+2*Math.floor((high-low)/3)+1,high];
  const a=Math.max(low,parseNoteText(el.rangeMin.value));
  const b=Math.min(high,parseNoteText(el.rangeMax.value));
  if(a>b)throw new Error('指定した音域が楽器の発音可能範囲と合っていません');
  return [a,b];
}
function speechEnabled(control){return el.speech.value==='on' && !!control?.checked;}
async function announceInstrument(instrument){if(speechEnabled(el.instrumentSpeech))await speak(instrumentNames[instrument]||instrument,'ja-JP');}
async function requestWakeLock(){
  if(!('wakeLock' in navigator))return;
  try{wakeLock=await navigator.wakeLock.request('screen');wakeLock.addEventListener('release',()=>{wakeLock=null;});}catch(_){}
}
async function releaseWakeLock(){if(wakeLock){try{await wakeLock.release();}catch(_){}wakeLock=null;}}
function updateSettingsVisibility(){
  const melody=el.mode.value==='4';
  el.melodySettings.classList.toggle('hidden',!melody);
  el.ordinaryRange.classList.toggle('hidden',melody);
  el.customRange.classList.toggle('hidden',melody || el.range.value!=='4');
  el.progressionSettings.classList.toggle('hidden',el.mode.value!=='3');
  document.querySelectorAll('[data-speech-mode]').forEach(node=>node.classList.toggle('hidden',node.dataset.speechMode!==el.mode.value));
  el.progressionKeyWrap.classList.toggle('hidden',el.progressionKeyMode.value!=='1');
  el.melodyKey.disabled=el.melodyKeyMode.value!=='0';
  el.melodyScale.disabled=el.melodyScaleMode.value!=='0';
  el.nameType.disabled=['1','3'].includes(el.mode.value);
  if(el.nameType.disabled)el.nameType.value='0';
}
function updateMelodyScales(){
  const category=Object.keys(D.SCALE_CATEGORIES)[Number(el.melodyCategory.value)] || Object.keys(D.SCALE_CATEGORIES)[0];
  const list=D.SCALE_CATEGORIES[category];
  const old=el.melodyScale.value;
  el.melodyScale.innerHTML='';
  list.forEach((name,i)=>el.melodyScale.add(new Option(name,String(i))));
  if(list.includes(old))el.melodyScale.value=String(list.indexOf(old));
}
function populateSettings(){
  D.NAMES.forEach((name,i)=>el.melodyKey.add(new Option(name,String(i))));
  Object.keys(D.SCALE_CATEGORIES).forEach((name,i)=>el.melodyCategory.add(new Option(name,String(i))));
  updateMelodyScales();
}

async function initializeAudio(targets){
  el.soundStatus.textContent='音源を読み込み中…（初回は少し時間がかかります）';
  if(!audioContext){
    const Ctx=window.AudioContext||window.webkitAudioContext;
    if(!Ctx)throw new Error('このブラウザはWeb Audio APIに対応していません');
    audioContext=new Ctx({latencyHint:'interactive'});
  }
  await audioContext.resume();
  if(!workletReady){
    const workletURL='https://cdn.jsdelivr.net/npm/spessasynth_lib@4.4.0/dist/spessasynth_processor.min.js';
    await audioContext.audioWorklet.addModule(workletURL);
    workletReady=true;
  }
  for(const instrument of targets){
    if(synths.has(instrument))continue;
    const response=await fetch(SOUND_FILES[instrument]);
    if(!response.ok)throw new Error(`${instrumentNames[instrument]}のSF2を読み込めません（${response.status}）`);
    const compressed=await response.arrayBuffer();
    if(!('DecompressionStream' in window))throw new Error('このSafariはgzip展開に対応していません。iOSを最新版に更新してください');
    const stream=new Blob([compressed]).stream().pipeThrough(new DecompressionStream('gzip'));
    const bank=await new Response(stream).arrayBuffer();
    const synth=new WorkletSynthesizer(audioContext);
    synth.connect(audioContext.destination);
    await synth.isReady;
    await synth.soundBankManager.addSoundBank(bank,instrument);
    synths.set(instrument,synth);
  }
  el.soundStatus.textContent='音源：読み込み完了';
}
function noteOn(instrument,note,velocity=100){
  const synth=synths.get(instrument);
  if(!synth)throw new Error('音源が初期化されていません');
  synth.noteOn(0,note,Math.round(velocity*127/100));
  activeNotes.push({instrument,note});
}
function noteOff(instrument,note){
  const synth=synths.get(instrument);
  if(synth){try{synth.noteOff(0,note);}catch(_){}}
  activeNotes=activeNotes.filter(x=>!(x.instrument===instrument&&x.note===note));
}
function stopAllNotes(){
  for(const n of activeNotes.slice())noteOff(n.instrument,n.note);
  activeNotes=[];
}
function playNoteSet(instrument,notes){
  stopAllNotes();
  for(const n of notes)noteOn(instrument,n);
}
function formatRemaining(ms){const s=Math.max(0,Math.ceil(ms/1000));return `${String(Math.floor(s/60)).padStart(2,'0')}:${String(s%60).padStart(2,'0')}`;}
function updateTimer(){
  const left=endAt-Date.now();
  el.remaining.textContent='残り時間：'+formatRemaining(left);
  if(left<=0&&playing)stopSession('時間終了');
}
function setDisplay(text,instrument,status,kind='normal'){
  // Render each line separately so mobile text can be sized by its role.
  el.answer.replaceChildren();
  el.answer.className='answer-'+kind;
  String(text).split('\n').forEach((line,index)=>{
    const span=document.createElement('span');
    span.className='answer-line answer-line-'+index;
    span.textContent=line;
    el.answer.appendChild(span);
  });
  el.instrumentLabel.textContent='楽器：'+(instrumentNames[instrument]||'---');
  el.status.textContent=status||'再生中';
}
function setMelodyDisplay(melody,sequence,index){
  el.answer.replaceChildren();el.answer.className='answer-melody';
  const addLine=(text,cls)=>{const span=document.createElement('span');span.className=cls;span.textContent=text;el.answer.appendChild(span);};
  addLine(`キー：${D.NAMES[melody.key]} / 音階：${melody.scaleName}`,'answer-line answer-line-0');
  const line=document.createElement('span');line.className='answer-line answer-line-1 melody-sequence';
  melody.notes.forEach((note,i)=>{if(i){const arrow=document.createElement('span');arrow.textContent=' → ';line.appendChild(arrow);}const n=document.createElement('span');n.textContent=noteName(note);if(i===index)n.classList.add('current-note');line.appendChild(n);});
  el.answer.appendChild(line);
  addLine(`${index+1} / ${melody.notes.length}`,'answer-line answer-line-2');
  el.instrumentLabel.textContent='楽器：'+(instrumentNames[melody.instrument]||'---');
  el.status.textContent=`メロディ再生中 ${index+1}/${melody.notes.length}`;
}
function getRangeForMelody(instrument){
  const name=el.melodyRange.value;
  let [low,high]=D.MELODY_RANGES[name];
  const [il,ih]=D.RANGES[instrument];
  low=Math.max(low,il);high=Math.min(high,ih);
  if(low>high)throw new Error('選択した楽器とメロディ音域が一致しません');
  return [low,high];
}
function generateSingleNote(){
  const instrument=chooseInstrument();
  const [low,high]=getSelectedRange(instrument);
  let choices=Array.from({length:high-low+1},(_,i)=>low+i);
  if(choices.length>1&&choices.includes(previousNote))choices=choices.filter(n=>n!==previousNote);
  const note=pick(choices);previousNote=note;return {instrument,note};
}
function generateInterval(){
  const instrument=chooseInstrument();
  const [low,high]=getSelectedRange(instrument);
  const semitones=Object.keys(D.INTERVALS).map(Number).filter(n=>high-low>=n);
  if(!semitones.length)throw new Error('選択した音域が狭すぎて音程を生成できません');
  const gap=pick(semitones),direction=pick(['上昇','下降']);
  const first=direction==='上昇'?Math.floor(Math.random()*(high-gap-low+1))+low:Math.floor(Math.random()*(high-(low+gap)+1))+low+gap;
  return {instrument,first,second:direction==='上昇'?first+gap:first-gap,gap,direction};
}
function getGuitarVoicings(root,intervals,inversion,instrument,maxFret){
  const [low,high]=D.RANGES[instrument];
  const pcs=new Set(intervals.map(x=>(root+x)%12));
  const targetBass=(root+intervals[inversion])%12;
  const stringOptions=D.GUITAR_OPEN_STRINGS.map(open=>{
    const options=[null];
    for(let fret=0;fret<=maxFret;fret++){
      const note=open+fret;
      if(note>=low&&note<=high&&pcs.has(note%12))options.push(fret);
    }
    return options;
  });
  const results=[];
  function visit(index,frets){
    if(index<stringOptions.length){for(const fret of stringOptions[index])visit(index+1,[...frets,fret]);return;}
    const notes=frets.map((f,i)=>f===null?null:D.GUITAR_OPEN_STRINGS[i]+f).filter(x=>x!==null);
    if(notes.length<4)return;
    const used=new Set(notes.map(n=>n%12));
    if([...pcs].some(pc=>!used.has(pc)))return;
    if(notes[0]%12!==targetBass)return;
    if(notes.some((n,i)=>i>0&&n<notes[i-1]))return;
    const pressed=frets.filter(f=>f!==null&&f>0);
    if(pressed.length&&(Math.max(...pressed)-Math.min(...pressed)>4||new Set(pressed).size>4))return;
    results.push({frets,notes});
  }
  visit(0,[]);return results;
}
function generateGuitarChord(instrument){
  for(let attempt=0;attempt<100;attempt++){
    const name=pick(Object.keys(D.CHORD_TYPES));
    const intervals=D.CHORD_TYPES[name];
    const inversion=Math.floor(Math.random()*intervals.length);
    const root=Math.floor(Math.random()*12);
    const maxFret=pick([5,7,9,12]);
    let candidates=getGuitarVoicings(root,intervals,inversion,instrument,maxFret);
    if(!candidates.length)candidates=getGuitarVoicings(root,intervals,inversion,instrument,12);
    if(candidates.length){const v=pick(candidates);return {name,root,inversion,notes:v.notes,frets:v.frets};}
  }
  throw new Error('演奏可能なギターコードを生成できませんでした');
}
function generateProgressionChord(chordData,instrument,key){
  const [offset,type,degree,spoken]=chordData;
  const root=(key+offset)%12,intervals=D.CHORD_TYPES[type];
  const candidates=getGuitarVoicings(root,intervals,0,instrument,12);
  if(!candidates.length)throw new Error('ギターで演奏可能なコードフォームが見つかりませんでした');
  const v=pick(candidates);return {name:type,root,inversion:0,notes:v.notes,frets:v.frets,degree,spoken};
}
function generateMelody(){
  const instrument=chooseInstrument();
  const [low,high]=getRangeForMelody(instrument);
  const count=Number(el.melodyCount.value)===0?3+Math.floor(Math.random()*6):Number(el.melodyCount.value);
  const key=el.melodyKeyMode.value==='1'?Math.floor(Math.random()*12):Number(el.melodyKey.value);
  const allScales=Object.values(D.SCALE_CATEGORIES).flat();
  const scaleName=el.melodyScaleMode.value==='1'?pick(allScales):D.SCALE_CATEGORIES[Object.keys(D.SCALE_CATEGORIES)[Number(el.melodyCategory.value)]][Number(el.melodyScale.value)];
  let candidates=Array.from({length:high-low+1},(_,i)=>low+i);
  if(el.melodySelection.value==='1'){
    const allowed=new Set(D.SCALES[scaleName].map(x=>(key+x)%12));
    candidates=candidates.filter(n=>allowed.has(n%12));
  }
  if(!candidates.length)throw new Error('選択した条件では音を生成できません');
  return {instrument,notes:Array.from({length:count},()=>pick(candidates)),key,scaleName};
}
function inversionName(index){return D.INVERSION_NAMES[index]||'';}
function chordLabel(chord){return D.NAMES[chord.root%12]+(D.CHORD_DISPLAY_NAMES[chord.name]||chord.name);}
function noteSpeech(note){
  const pitch=note%12,japanese=el.nameType.value==='1';
  let text=(japanese?D.JAPANESE_SPEECH_NAMES:D.ENGLISH_SPEECH_NAMES)[pitch];
  if(el.octave.value==='0')text+=' '+(japanese?String(Math.floor(note/12)-1):(D.OCTAVE_ENGLISH[Math.floor(note/12)-1]||String(Math.floor(note/12)-1)));
  return {text,lang:japanese?'ja-JP':'en-US'};
}
function primeSpeechFromUserGesture(){
  if(!('speechSynthesis'in window)||!('SpeechSynthesisUtterance'in window))return;
  // Must be called synchronously from the Start button tap on iOS Safari.
  // A nearly silent utterance activates the speech engine before soundfont fetches await.
  try{
    const synth=window.speechSynthesis;
    const primer=new SpeechSynthesisUtterance('あ');
    primer.lang='ja-JP';primer.volume=0.01;primer.rate=1;
    synth.cancel();
    synth.speak(primer);
    speechPrimePromise=new Promise(resolve=>{
      let settled=false;
      const finish=()=>{if(settled)return;settled=true;clearTimeout(timer);speechPrimed=true;resolve();};
      primer.onend=finish;primer.onerror=finish;
      const timer=setTimeout(finish,1800);
    });
  }catch(_){speechPrimePromise=Promise.resolve();}
}

function speak(text,lang){
  if(el.speech.value!=='on'||!text)return Promise.resolve();
  if(!('speechSynthesis'in window)||!('SpeechSynthesisUtterance'in window)){el.status.textContent='このブラウザでは音声読み上げを利用できません';return Promise.resolve();}
  return new Promise(resolve=>{
    const utterance=new SpeechSynthesisUtterance(text);
    utterance.lang=lang||'en-US';utterance.rate=Number(el.speed.value);
    let settled=false;
    let watchdog;
    const finish=()=>{if(settled)return;settled=true;clearTimeout(watchdog);resolve();};
    utterance.onend=finish;utterance.onerror=finish;
    watchdog=setTimeout(()=>{try{speechSynthesis.cancel();}catch(_){}finish();},30000);
    try{const synth=window.speechSynthesis;synth.resume();synth.speak(utterance);if(synth.paused)synth.resume();}catch(_){finish();}
  });
}
async function speakSingle(note){const s=noteSpeech(note);await speak(s.text,s.lang);}
async function speakInterval(gap){const label=D.INTERVALS[String(gap)];if(label)await speak(label,'ja-JP');}
async function speakChord(chord){
  let text=D.ENGLISH_SPEECH_NAMES[chord.root]+' '+D.CHORD_SPEECH_EN[chord.name]+', '+D.INVERSION_SPEECH_EN[chord.inversion];
  for(const n of chord.notes){text+=', '+D.ENGLISH_SPEECH_NAMES[n%12];if(el.octave.value==='0')text+=' '+(D.OCTAVE_ENGLISH[Math.floor(n/12)-1]||String(Math.floor(n/12)-1));}
  await speak(text,'en-US');
}
async function speakProgression(progression,key){
  const mode=progression.mode==='major'?'メジャー':'マイナー';
  const keyText=D.NAMES[key]+mode;
  const degrees=progression.chords.map(c=>c[3]).join('、');
  const name=D.PROGRESSION_READINGS[progression.name]||progression.name.split('').join('、');
  await speak(keyText+'。コード進行は、'+degrees+'。'+name,'ja-JP');
}
async function speakMelody(melody){
  if(speechEnabled(el.melodyKeySpeech)){
    const keyName=D.ENGLISH_SPEECH_NAMES[melody.key];
    await speak(keyName,'en-US');
  }
  if(speechEnabled(el.melodyNotesSpeech)){
    const japanese=el.nameType.value==='1';
    const notes=melody.notes.map(n=>{
      const p=n%12;let t=(japanese?D.JAPANESE_SPEECH_NAMES:D.ENGLISH_SPEECH_NAMES)[p];
      if(el.octave.value==='0')t+=' '+(japanese?String(Math.floor(n/12)-1):(D.OCTAVE_ENGLISH[Math.floor(n/12)-1]||String(Math.floor(n/12)-1)));
      return t;
    }).join(japanese?'、':', ');
    await speak(notes,japanese?'ja-JP':'en-US');
  }
  if(speechEnabled(el.melodyScaleSpeech)){
    const japanese=el.nameType.value==='1';
    const scaleText=(japanese?D.SCALE_JAPANESE_NAMES:D.SCALE_ENGLISH_NAMES)[melody.scaleName]||melody.scaleName;
    await speak(scaleText,japanese?'ja-JP':'en-US');
  }
}
async function playFor(instrument,notes,ms,token){
  if(token!==runToken)return;
  await audioContext.resume();
  playNoteSet(instrument,notes);
  await sleep(ms);
  if(token!==runToken)return;
  stopAllNotes();
}
function fretText(frets){return frets.map(f=>f===null?'x':String(f)).join('-');}
async function runSingle(token){
  const q=generateSingleNote();
  setDisplay(noteName(q.note),q.instrument,'単音再生中');
  await announceInstrument(q.instrument);
  if(token!==runToken)return;
  await playFor(q.instrument,[q.note],durationSec*1000,token);
  if(token!==runToken)return;
  if(speechEnabled(el.singleNoteSpeech)){
    setDisplay(noteName(q.note),q.instrument,'音名を読み上げ中');
    await speakSingle(q.note);
  }
  if(token===runToken)await sleep(intervalSec*1000);
}
async function runChord(token){
  const instrument=chooseInstrument(),chord=generateGuitarChord(instrument);
  const notes=chord.notes;
  setDisplay(chordLabel(chord)+' / '+inversionName(chord.inversion)+'\n'+notes.map(noteName).join(' - '),instrument,'コード再生中');
  el.status.textContent='フォーム（6弦→1弦）：'+fretText(chord.frets);
  await announceInstrument(instrument);
  if(token!==runToken)return;
  await playFor(instrument,notes,durationSec*1000,token);
  if(token!==runToken)return;
  if(speechEnabled(el.chordSpeech)){
    el.status.textContent='コード名を読み上げ中';
    await speakChord(chord);
  }
  if(token===runToken)await sleep(intervalSec*1000);
}
async function runInterval(token){
  const q=generateInterval();
  const intervalLabel=D.INTERVALS[String(q.gap)]||'音程不明（'+q.gap+'半音）';
  await announceInstrument(q.instrument);
  if(token!==runToken)return;
  setDisplay('1音目：'+noteName(q.first)+'\n'+intervalLabel+'（'+q.direction+'）',q.instrument,'音程再生中（1音目）');
  await playFor(q.instrument,[q.first],durationSec*1000,token);
  if(token!==runToken)return;
  if(intervalSec>0)await sleep(intervalSec*1000);
  if(token!==runToken)return;
  setDisplay('2音目：'+noteName(q.second)+'\n'+intervalLabel+'（'+q.direction+'）',q.instrument,'音程再生中（2音目）');
  await playFor(q.instrument,[q.second],durationSec*1000,token);
  if(token!==runToken)return;
  if(speechEnabled(el.intervalSpeech)){
    el.status.textContent='音程名を読み上げ中';
    await speakInterval(q.gap);
  }
  if(token===runToken)await sleep(intervalSec*1000);
}
async function runProgression(token){
  const history=[];
  const genre=el.genre.value;
  const choices=D.PROGRESSIONS.filter(p=>genre==='すべて'||p.genre===genre);
  if(!choices.length)throw new Error('選択されたジャンルに進行がありません');
  const progression=pick(choices);
  const key=el.progressionKeyMode.value==='0'?Math.floor(Math.random()*12):parseKeyText(el.progressionKey.value);
  const instrument=chooseInstrument();
  await announceInstrument(instrument);
  for(let i=0;i<progression.chords.length;i++){
    if(token!==runToken)return;
    const chord=generateProgressionChord(progression.chords[i],instrument,key);
    history.push([chordLabel(chord),progression.chords[i][2]]);
    const historyText=history.map(item=>item[0]+'（'+item[1]+'）').join(' → ');
    setDisplay(D.NAMES[key]+(progression.mode==='major'?'メジャー':'マイナー')+' / '+progression.name+'\n'+historyText,instrument,`コード進行 ${i+1}/${progression.chords.length}`);
    await playFor(instrument,chord.notes,durationSec*1000,token);
    if(i<progression.chords.length-1&&intervalSec>0)await sleep(intervalSec*1000);
  }
  if(token!==runToken)return;
  if(speechEnabled(el.progressionSpeech)){
    el.status.textContent='コード進行を読み上げ中';
    await speakProgression(progression,key);
  }
  if(token===runToken)await sleep(intervalSec*1000);
}
async function runMelody(token){
  const melody=generateMelody();
  const sequence=melody.notes.map(noteName).join(' → ');
  await announceInstrument(melody.instrument);
  for(let i=0;i<melody.notes.length;i++){
    if(token!==runToken)return;
    setMelodyDisplay(melody,sequence,i);
    await playFor(melody.instrument,[melody.notes[i]],durationSec*1000,token);
    if(token!==runToken)return;
    if(i<melody.notes.length-1&&intervalSec>0)await sleep(intervalSec*1000);
  }
  if(token!==runToken)return;
  await speakMelody(melody);
  if(token===runToken)await sleep(intervalSec*1000);
}
async function sessionLoop(token){
  while(playing&&token===runToken&&Date.now()<endAt){
    switch(el.mode.value){
      case '0':await runSingle(token);break;
      case '1':await runChord(token);break;
      case '2':await runInterval(token);break;
      case '3':await runProgression(token);break;
      case '4':await runMelody(token);break;
    }
  }
  if(token===runToken&&playing)stopSession('時間終了');
}
function validateSettings(){
  const minutes=Number(el.minutes.value),duration=Number(el.duration.value),interval=Number(el.interval.value);
  if(!Number.isFinite(minutes)||minutes<0.1||minutes>600)throw new Error('再生時間は0.1〜600分で指定してください');
  if(!Number.isFinite(duration)||duration<=0)throw new Error('音の長さは0秒より大きくしてください');
  if(!Number.isFinite(interval)||interval<0)throw new Error('音と音の間隔は0秒以上で指定してください');
  if(['0','2'].includes(el.mode.value)){
    for(const instrument of (selectedInstrument()==='ランダム'?INSTRUMENTS:[selectedInstrument()]))getSelectedRange(instrument);
  }
  if(el.mode.value==='4'){
    const possible=selectedInstrument()==='ランダム'?INSTRUMENTS:[selectedInstrument()];
    if(!possible.some(inst=>{const [a,b]=D.MELODY_RANGES[el.melodyRange.value];const [c,d]=D.RANGES[inst];return Math.max(a,c)<=Math.min(b,d);}))throw new Error('選択した楽器とメロディ音域が一致しません');
  }
  if(el.mode.value==='3'&&el.progressionKeyMode.value==='1')parseKeyText(el.progressionKey.value);
  durationSec=duration;intervalSec=interval;return minutes;
}
async function startSession(){
  if(playing)return;
  if(el.speech.value==='on')primeSpeechFromUserGesture();
  let minutes,targets;
  try{
    minutes=validateSettings();
    targets=selectedInstrument()==='ランダム'?INSTRUMENTS:[selectedInstrument()];
  }catch(e){el.status.textContent=e.message;return;}
  el.start.disabled=true;el.stop.disabled=true;el.status.textContent='音源を準備しています…';
  try{
    await initializeAudio(targets);
    if(el.speech.value==='on')await speechPrimePromise;
    if(!audioContext)throw new Error('オーディオを初期化できませんでした');
    await audioContext.resume();
    await requestWakeLock();
    playing=true;runToken++;const token=runToken;
    endAt=Date.now()+minutes*60000;previousNote=-1;
    el.stop.disabled=false;el.status.textContent='トレーニング中';
    timerTicker=setInterval(updateTimer,250);updateTimer();
    sessionLoop(token).catch(err=>{if(token===runToken){stopSession('再生エラー：'+err.message);}});
  }catch(e){
    el.status.textContent='音源読み込みエラー：'+e.message;
    el.start.disabled=false;el.stop.disabled=true;
    el.soundStatus.textContent='音源：読み込みに失敗しました';
  }
}
function stopSession(reason='停止しました'){
  if(!playing&&el.start.disabled===false)return;
  playing=false;runToken++;clearTimers();
  if(timerTicker){clearInterval(timerTicker);timerTicker=null;}
  stopAllNotes();
  try{if('speechSynthesis'in window)speechSynthesis.cancel();}catch(_){}
  try{audioContext?.suspend();}catch(_){}
  releaseWakeLock();
  el.start.disabled=false;el.stop.disabled=true;
  el.status.textContent=reason;el.remaining.textContent='残り時間：00:00';
  if(reason==='時間終了')el.answer.textContent='終了';
}

el.mode.addEventListener('change',updateSettingsVisibility);
el.range.addEventListener('change',updateSettingsVisibility);
el.melodyKeyMode.addEventListener('change',updateSettingsVisibility);
el.melodyScaleMode.addEventListener('change',updateSettingsVisibility);
el.melodyCategory.addEventListener('change',updateMelodyScales);
el.progressionKeyMode.addEventListener('change',updateSettingsVisibility);
el.speed.addEventListener('input',()=>el.speedValue.textContent=Number(el.speed.value).toFixed(2));
el.start.addEventListener('click',startSession);
el.stop.addEventListener('click',()=>stopSession('停止しました'));
window.addEventListener('pagehide',()=>{stopSession('停止しました');try{audioContext?.suspend();}catch(_){}});
document.addEventListener('visibilitychange',()=>{if(document.visibilityState==='visible'&&playing&&!wakeLock)requestWakeLock();});

populateSettings();updateSettingsVisibility();
