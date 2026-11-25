import { WorkletSynthesizer } from "https://esm.sh/spessasynth_lib@4.4.0";

const D = await fetch('./app-data.json').then(r => { if (!r.ok) throw new Error('設定データを読み込めません'); return r.json(); });
const INSTRUMENTS = await fetch('./instruments.json').then(r => { if (!r.ok) throw new Error('楽器一覧を読み込めません'); return r.json(); });
const $ = id => document.getElementById(id);
const el = {
  instrument:$('instrument'), mode:$('mode'), range:$('range'), customRange:$('customRange'), rangeMin:$('rangeMin'), rangeMax:$('rangeMax'),
  ordinaryRange:$('ordinaryRange'), instrumentRange:$('instrumentRange'), melodySettings:$('melodySettings'), melodySelection:$('melodySelection'), melodyStyle:$('melodyStyle'), melodyComposition:$('melodyComposition'), melodyAccompStyle:$('melodyAccompStyle'), melodyVolume:$('melodyVolume'), accompanimentVolume:$('accompanimentVolume'), melodyKeyMode:$('melodyKeyMode'), melodyKey:$('melodyKey'),
  melodyScaleMode:$('melodyScaleMode'), melodyCategory:$('melodyCategory'), melodyScale:$('melodyScale'), melodyCount:$('melodyCount'), melodyRange:$('melodyRange'), melodyRhythm:$('melodyRhythm'), melodyMeter:$('melodyMeter'), melodyTempo:$('melodyTempo'), melodyContinuity:$('melodyContinuity'),
  minutes:$('minutes'), instrumentVolume:$('instrumentVolume'), speechVolume:$('speechVolume'), octaveGap:$('octaveGap'), duration:$('duration'), soundGap:$('soundGap'), questionGap:$('questionGap'), speech:$('speech'), speechModes:$('speechModes'), speed:$('speed'), speedValue:$('speedValue'),
  genre:$('genre'), progressionSource:$('progressionSource'), progressionInversion:$('progressionInversion'), progressionSettings:$('progressionSettings'), progressionKeyMode:$('progressionKeyMode'), progressionKeyWrap:$('progressionKeyWrap'), progressionKey:$('progressionKey'),
  answer:$('answer'), instrumentLabel:$('instrumentLabel'), status:$('status'), remaining:$('remaining'), soundStatus:$('soundStatus'), loadBar:$('loadBar'), loadPercent:$('loadPercent'), start:$('start'), stop:$('stop')
};

const CATEGORIES = [...new Set(INSTRUMENTS.map(x=>x.category))];
const instrumentById = new Map(INSTRUMENTS.map(x=>[x.id,x]));
let audioContext=null, synth=null, soundLoaded=false, loadingPromise=null;
let runToken=0, playing=false, endAt=0, durationSec=1, soundGapSec=0.5, questionGapSec=1;
let activeTimers=new Set(), activeNotes=[], previousNote=-1, timerTicker=null, wakeLock=null, speechPrimePromise=Promise.resolve();
let songMelodyMotifs=new Map(), songArrangementMotifs=new Map();
// Phrase-level memory: reusable relative melodic shapes, not isolated random pitches.
let songPhraseThemes=new Map(), songBassMemory=new Map();
let accompanimentVoicing=null, arrangementVoicing=new Map(), songInstrumentation=new Map();
let arrangementMotifPatterns=new Map(), lastSongCycle=-1, pendingSongTransition=false;
function songCycleAt(bar){return track14?.id??Math.floor(Math.max(0,bar)/SONG_FORM_LENGTH);}
function newSongBoundary(bar){return track14?bar===track14.end:bar>0&&bar%SONG_FORM_LENGTH===0;}
function songEnding(bar){const section=songSectionAt(bar);return section.name==='アウトロ'&&section.offset>=section.bars-2;}
function songPartEnabled(id,bar){
 if(musicGoal()!=='song')return true;
 const section=songSectionAt(bar),person=personalityAt(bar),cycle=songCycleAt(bar);
 const k=cycle+':'+id;
 if(!songInstrumentation.has(k)){
  const probability=id==='leadLayer2'?.73:id==='backingLayer2'?.83:.96;
  songInstrumentation.set(k,Math.random()<probability);
  if(songInstrumentation.size>64)songInstrumentation.delete(songInstrumentation.keys().next().value);
 }
 return songInstrumentation.get(k)&&!(section.name==='イントロ'&&id==='leadLayer2')&&!(section.name==='アウトロ'&&section.offset>=section.bars-2&&id!=='backingLayer1');
}
function chooseSmoothVoicing(chord,melody,inst,previous){
 if(!chord||!inst)return [];
 const lo=inst.range[0],hi=inst.range[1],pcs=[...new Set(chord.pcs)];
 const candidates=[];
 for(let center=Math.max(lo+5,melody-24);center<=Math.min(hi-5,melody+16);center+=3){
  const notes=pcs.map(pc=>{
   let best=null,dist=Infinity;
   for(let n=lo;n<=hi;n++)if(n%12===pc){const d=Math.abs(n-center);if(d<dist){best=n;dist=d;}}
   return best;
  });
  if(notes.some(n=>n===null)||new Set(notes).size!==notes.length)continue;
  notes.sort((a,b)=>a-b);
  const overlap=notes.reduce((v,n)=>v+Math.max(0,9-Math.abs(n-melody))*1.5,0);
  const motion=previous?.length?notes.reduce((v,n)=>v+Math.min(...previous.map(x=>Math.abs(n-x))),0):0;
  const crowd=notes.reduce((v,n,i)=>v+(i&&n-notes[i-1]<3?3:0),0);
  const spread=Math.max(0,notes.at(-1)-notes[0]-19);
  candidates.push({notes,score:motion*1.9+overlap+crowd+spread});
 }
 return candidates.sort((a,b)=>a.score-b.score)[0]?.notes||accompanimentNotes(chord,melody,inst);
}
// V6: stable song-level arrangement identity, varied between complete forms.
let songSoundIdentity=new Map(),songBassContour=new Map();
function songIdentity(bar){
 const cycle=songCycleAt(bar);
 if(!songSoundIdentity.has(cycle)){
  const personality=personalityAt(bar);
  songSoundIdentity.set(cycle,{room:.08+Math.random()*.16,variation:.12+Math.random()*.24,
   bassMotion:personality.genre==='ジャズ'?.75:personality.genre==='ロック'?.48:.55,
   contrast:Math.random()*.35,leadSpace:.12+Math.random()*.14});
  if(songSoundIdentity.size>8) songSoundIdentity.delete(songSoundIdentity.keys().next().value);
 }
 return songSoundIdentity.get(cycle);
}
function expressiveRest(r,bar,part='lead'){
 if(!r||musicGoal()!=='song')return false;
 const section=songSectionAt(bar),identity=songIdentity(bar);
 if(section.name==='サビ'&&part==='lead')return false;
 const atEnd=r.phraseEnd||section.offset%4===3;
 if(part==='lead')return atEnd&&r.beatPosition>=2&&Math.random()<identity.leadSpace;
 return atEnd&&r.beatPosition>=2&&Math.random()<.42;
}
function enhancedVoicing(chord,melody,inst,previous,bar){
 const base=chooseSmoothVoicing(chord,melody,inst,previous);
 if(!base.length||musicGoal()!=='song')return base;
 const personality=personalityAt(bar),role=instrumentRole(inst);
 if(role==='bass'||role==='wind'||personality.complexity<.7||base.length>=5)return base;
 // Add a consonant 9th only when it does not clash with the lead or crowd the chord.
 const ninth=(chord.root+2)%12;
 if(Math.random()>.16+personality.complexity*.20||Math.abs((melody%12)-ninth)<=1)return base;
 const lo=inst.range[0],hi=inst.range[1];
 const options=[];for(let n=lo;n<=hi;n++)if(n%12===ninth&&Math.abs(n-melody)>=5&&base.every(x=>Math.abs(x-n)>=3))options.push(n);
 if(!options.length)return base;
 const target=base[Math.floor(base.length/2)];
 const n=options.reduce((a,b)=>Math.abs(a-target)<=Math.abs(b-target)?a:b);
 return [...base,n].sort((a,b)=>a-b);
}
function melodyVariantWeight(i,plan,previous,n,anchor){
 if(!plan||musicGoal()!=='song')return 1;
 // Separate rhythmic identity from pitch identity: a familiar motif may be transposed or inverted.
 const section=songSectionAt(plan.bar),cycle=songCycleAt(plan.bar);
 const identity=songIdentity(plan.bar);
 const transform=(section.name==='サビ'&&section.offset>=8)?1:(section.name==='Aメロ'&&section.offset>=8)?-1:0;
 if(!transform)return 1;
 const target=anchor+transform*3+(previous-anchor)*.20;
 return Math.exp(-Math.abs(n-target)*identity.variation*.07);
}
function performanceVelocity(base,bar,beat,part='lead'){
 const identity=songIdentity(bar),energy=musicalEnergy(bar);
 const accent=grooveAccent(bar,beat)?5:0;
 const roleBias=part==='lead'?6:part==='bass'?0:-7;
 const phrase=songSectionAt(bar),build=phrase.offset%8/8;
 return Math.max(24,Math.min(115,Math.round(base+roleBias+accent+energy*9+build*5+(Math.random()-.5)*4)));
}
function arrangementQuality(m){
 let penalty=0;
 for(let i=1;i<m.notes.length;i++){
  const leap=Math.abs(m.notes[i]-m.notes[i-1]);
  if(leap>9)penalty+=leap-9;
  if(m.rhythm?.[i]?.phraseEnd&&m.harmony?.[i]&&!m.harmony[i].notes.has(m.notes[i]%12))penalty+=3;
 }
 return penalty;
}

function phraseIdentity(r){
 const section=songSectionAt(r.measure);
 const family=section.name==='サビ'?'chorus':section.name==='Aメロ'?'verse':section.name==='Bメロ'?'prechorus':section.name;
 return family+':'+Math.floor(section.offset/4)%2;
}
function phraseMotionTarget(r,key,anchor){
 const section=songSectionAt(r.measure),part=(r.measure%4),beat=r.beatPosition;
 const climb=section.name==='サビ'?2:section.name==='Bメロ'?1:0;
 const answer=section.offset%8>=4;
 const arc=(answer?[-1,1,2,-2]:[-2,0,3,1])[part]+climb;
 return anchor+arc+(beat>=2?1:0);
}

const SONG_FORM=[{name:'イントロ',bars:4,energy:0.27},{name:'Aメロ',bars:16,energy:0.42},{name:'Bメロ',bars:8,energy:0.67},{name:'サビ',bars:16,energy:0.94},{name:'間奏',bars:8,energy:0.52},{name:'Aメロ',bars:8,energy:0.49},{name:'サビ',bars:16,energy:1},{name:'アウトロ',bars:8,energy:0.24}];
const SONG_FORM_LENGTH=SONG_FORM.reduce((n,x)=>n+x.bars,0);
let track14=null, serial14=0;
function design14(start){
 const person=pick(SONG_PERSONALITIES.filter(p=>p!==track14?.person));
 const mode=el.melodyMeter?.value||'4/4';
 const meter=mode==='random'?pick(['4/4','3/4','6/8','2/4','5/4'].filter(x=>x!==track14?.meter)):mode;
 const bpm=Math.max(40,Math.min(240,(Number(el.melodyTempo?.value)||100)*person.tempo*(.9+Math.random()*.2)));
 const unit=4*METER_BEATS[meter]*60/bpm, target=120+Math.random()*180;
 const blocks=Math.max(Math.ceil(120/unit),Math.min(Math.floor(300/unit),Math.round(target/unit)));
 const forms=[['イントロ','Aメロ','Bメロ','サビ','間奏','Aメロ','サビ','アウトロ'],['Aメロ','サビ','Aメロ','Bメロ','サビ','アウトロ'],['イントロ','Aメロ','Bメロ','サビ','間奏','Bメロ','サビ','アウトロ']];
 const names=pick(forms).slice();while(names.length>blocks){let j=names.findIndex(x=>['イントロ','間奏','Bメロ'].includes(x));names.splice(j<0?1:j,1);}
 const energy={'イントロ':.27,'Aメロ':.45,'Bメロ':.67,'サビ':.95,'間奏':.52,'アウトロ':.24};
 const form=names.map(name=>({name,bars:4,energy:energy[name]}));
 for(let i=form.length;i<blocks;i++)pick(form.filter(x=>x.name!=='アウトロ'&&x.name!=='イントロ')).bars+=4;
 return {id:++serial14,start,end:start+blocks*4,form,person,meter,bpm,key:null,scale:null};
}
function musicGoal(){return $('musicGoal')?.value||'song';}
// A personality belongs to a complete song, not to the entire training session.
// Retain it for 1–2 full forms, then deliberately change several dimensions.
const SONG_PERSONALITIES=[
 {name:'穏やかなバラード',genre:'J-POP',tempo:.79,density:.70,complexity:.65,syncopation:.32,range:.72,brightness:.30},
 {name:'軽快なポップス',genre:'J-POP',tempo:1.12,density:1.08,complexity:.8,syncopation:.65,range:1,brightness:.75},
 {name:'力強いロック',genre:'ロック',tempo:1.17,density:1.14,complexity:.48,syncopation:.53,range:1.06,brightness:.88},
 {name:'落ち着いたジャズ',genre:'ジャズ',tempo:.91,density:.82,complexity:1.20,syncopation:.83,range:.86,brightness:.42},
 {name:'躍動的なジャズ',genre:'ジャズ',tempo:1.10,density:1.02,complexity:1.35,syncopation:1,range:1.08,brightness:.82},
 {name:'叙情的なポップス',genre:'J-POP',tempo:.94,density:.85,complexity:1.05,syncopation:.47,range:.91,brightness:.46}
];
let songPersonality=null,songPersonalityCycle=-1,songPersonalityNextCycle=0,songPersonalityGeneration=0;
function personalityAt(bar){
 if(musicGoal()!=='song')return {name:'音感練習',genre:'J-POP',tempo:1,density:1,complexity:1,syncopation:.5,range:1,brightness:.5};
 const cycle=songCycleAt(bar);
 if(!songPersonality||cycle>=songPersonalityNextCycle){
  const options=SONG_PERSONALITIES.filter(x=>x!==songPersonality);
  songPersonality=track14?.person??pick(options.length?options:SONG_PERSONALITIES);
  songPersonalityGeneration++;
  songPersonalityNextCycle=cycle+1;
  songPhraseThemes.clear();songMelodyMotifs.clear();songBassContour.clear();songArrangementMotifs.clear();songGrooveMemory.clear();songBassMemory.clear();arrangementMotifPatterns.clear();arrangementVoicing.clear();accompanimentVoicing=null;
  songHarmony=null;songMotif=null;previousMelodyEnding=null;
  musicalKeyBlock=-1;musicalScaleBlock=-1;
 }
 songPersonalityCycle=cycle;
 return songPersonality;
}

function songSectionAt(bar){let pos=track14?Math.max(0,Math.min(track14.end-track14.start-1,bar-track14.start)):((bar%SONG_FORM_LENGTH)+SONG_FORM_LENGTH)%SONG_FORM_LENGTH;for(const x of (track14?.form??SONG_FORM)){if(pos<x.bars)return {...x,offset:pos};pos-=x.bars;}return {...SONG_FORM[0],offset:0};}
function musicalEnergy(bar){return musicGoal()==='training'?0.64:Math.min(1,songSectionAt(bar).energy*(.85+.16*personalityAt(bar).density));}
// Shared song-level phrasing plan: stable within each section, renewed on the next cycle.
const SONG_GROOVES={
 'J-POP':[[0,.5,1.5,2.5,3.5],[0,1,2,3],[0,.75,2,2.75]],
 'ロック':[[0,1,2,3],[0,.5,2,2.5],[0,1.5,2,3.5]],
 'ジャズ':[[0,1.5,2.5,3.5],[0,.67,1.67,2.67],[0,1,2.5,3.5]]
};
let songGrooveMemory=new Map(),songThemeMemory=new Map();
function grooveAt(bar){
 const section=songSectionAt(bar),genre=personalityAt(bar).genre;
 const key=songPersonalityGeneration+':'+genre+':'+section.name+':'+Math.floor(section.offset/4);
 if(!songGrooveMemory.has(key))songGrooveMemory.set(key,pick(SONG_GROOVES[genre]||SONG_GROOVES['J-POP']));
 return songGrooveMemory.get(key);
}
// V17: track-local emotional trajectory and recurring rhythmic identities.
// V18: scale/genre weighted trajectories and joint harmony/melody search.
const EMOTIONS18=[
 ['release',[.25,.48,.78,.38,.67,.88,.12]],['rise',[.12,.24,.48,.72,.53,.96,.16]],['wistful',[.45,.63,.82,.48,.76,.59,.22]],['dance',[.48,.35,.64,.83,.42,.91,.24]],
 ['dream',[.18,.32,.25,.49,.38,.58,.19]],['suspense',[.22,.42,.64,.82,.91,.65,.30]],['wave',[.35,.72,.28,.75,.32,.82,.18]],['heroic',[.30,.45,.62,.85,.58,.98,.28]],
 ['meditative',[.15,.24,.33,.28,.42,.31,.12]],['blues',[.48,.68,.43,.72,.49,.65,.35]],['shadow',[.58,.42,.76,.62,.88,.55,.32]],['floating',[.22,.48,.38,.57,.43,.68,.27]],
 ['late',[.15,.23,.35,.40,.58,.96,.18]],['early',[.32,.85,.53,.42,.65,.48,.20]],['unresolved',[.38,.55,.68,.47,.78,.72,.49]],['playful',[.32,.58,.42,.76,.38,.86,.22]]];
function scaleColor18(scale){const map={'リディアン':[6],'ドリアン':[9],'フリジアン':[1],'ミクソリディアン':[10],'ロクリアン':[6,1],'ハーモニックマイナー':[8,11],'メロディックマイナー':[9,11],'琉球音階':[4,11],'ハンガリアンマイナー':[6,8,11],'スパニッシュ':[1,4],'マイナーブルース':[6],'メジャーブルース':[3],'全音音階':[6,8]};return map[scale]||[];}
function chooseEmotionV18(t){const scale=t.scale||'',genre=t.person.genre;const preferred=scale.includes('リディアン')?['dream','floating','rise']:scale.includes('フリジアン')||scale.includes('ロクリアン')||scale.includes('ハンガリアン')||scale.includes('スパニッシュ')?['shadow','suspense','unresolved']:scale.includes('ブルース')?['blues','wave','wistful']:scale.includes('全音')||scale.includes('ディミニッシュ')?['floating','suspense','unresolved']:scale.includes('マイナー')||scale.includes('エオリアン')||scale.includes('短音階')?['wistful','release','late']:scale.includes('ドリアン')||scale.includes('ミクソリディアン')?['wave','dance','blues']:['rise','playful','heroic','meditative'];const genres=genre==='ジャズ'?['blues','floating','wave','unresolved']:genre==='ロック'?['heroic','late','dance','shadow']:['release','rise','wistful','playful'];const p=weightedChoice(EMOTIONS18,x=>1+4*preferred.includes(x[0])+2*genres.includes(x[0]));t.emotionName18=p[0];return p[1].map(v=>Math.max(.05,Math.min(.99,v+(Math.random()-.5)*.10)));}
function jointCompose18(queue){
 const groups=new Map();for(const m of queue)if(m.harmony)for(let i=0;i<m.notes.length;i++){const r=m.rhythm[i],h=m.harmony[i];if(!h)continue;const id=r.measure+':'+h.slot;if(!groups.has(id))groups.set(id,[]);groups.get(id).push({m,i,r,h});}
 let previous=null,prevNote=null,serial=0;const memory=new Map();if(songHarmony)songHarmony.groupHistory.clear();
 for(const rows of groups.values()){
 const {m,r,h}=rows[0],key=m.key,scale=D.SCALES[m.scaleName],sec=songSectionAt(r.measure),t=emotionV17(r.measure),color=scaleColor18(m.scaleName),genre=track14.person.genre;
 const pcs=scale.map(x=>(key+x)%12),pool=[];
 for(let d=0;d<pcs.length;d++)for(const q of (genre==='ジャズ'?['','m','dim','aug','maj7','m7','7','m7b5','sus4']:['','m','dim','aug','sus4','maj7','m7','7'])){const ns=CHORD_INTERVALS[q].map(x=>(pcs[d]+x)%12);if(ns.every(n=>pcs.includes(n)))pool.push({root:pcs[d],degree:d,quality:q,pcs:ns});}
 if(!pool.length)continue;
 const identity=sec.name+':'+(sec.offset%8)+':'+h.slot, remembered=memory.get(identity);let best=null;
 const desired=sec.name==='Bメロ'?[2,5,7,7]:sec.name==='サビ'?[0,9,5,7]:sec.name==='イントロ'?[0,0,5,0]:sec.name==='アウトロ'?[5,7,0,0]:[0,5,9,7];
 for(const c of pool){let cost=previous?voiceLeadingCost(previous,c)*.55:0;const rel=(c.root-key+12)%12;cost+=pitchDistance(rel,desired[sec.offset%4])*.22;cost+=previous?.root===c.root&&sec.offset%4!==0?.7:0;cost+=remembered&&remembered.root!==c.root?1.1:0;cost-=color.filter(x=>c.pcs.includes((key+x)%12)).length*(.25+t*.55);cost+=c.quality==='dim'||c.quality==='aug'?(1-t)*1.5:0; if(sec.offset===sec.bars-1&&sec.name==='Bメロ')cost+=rel===0?3:0;if(sec.name==='アウトロ'&&sec.offset===sec.bars-1)cost+=rel===0?-8:8;
 let last=prevNote,notes=[];for(const x of rows){const orig=x.m.notes[x.i],[lo,hi]=getRangeForMelody(x.m.inst);let win=orig,score=Infinity;for(let n=Math.max(lo,orig-3);n<=Math.min(hi,orig+3);n++){if(!pcs.includes(n%12))continue;const strong=x.r.beatPosition===0||x.r.beats>=1;let v=Math.abs(n-orig)*(x.r.hook21?4:.8)+(c.pcs.includes(n%12)?0:strong?1.7: .35)+(last===null?0:Math.max(0,Math.abs(n-last)-5)*.55);if(color.includes((n-key+120)%12))v-=.35+t*.35;if(v<score){score=v;win=n;}}notes.push(win);cost+=score/rows.length;last=win;}
 if(!best||cost<best.cost)best={c,notes,cost};}
 if(!best)continue;const c=best.c;memory.set(identity,c);const id=1800000+(++serial);const chord={...c,notes:new Set(c.pcs),inversion:0,measure:r.measure,slot:h.slot,harmonicStep:id,groupId:id,progressionName:'独自和声',progressionPosition:1,progressionLength:2};rows.forEach((x,j)=>{x.m.notes[x.i]=best.notes[j];x.m.harmony[x.i]=chord;x.m.chordInfos[x.i]=chordInfo(chord,key,m.scaleName,r.measure);});previous=c;prevNote=best.notes.at(-1);
 }
 for(const m of queue)m.themeTargets=[{indices:m.notes.map((_,i)=>i),ref:m.notes.map((n,i)=>({n,beats:m.rhythm[i].beats})),weight:8}];
}

function emotionV17(bar){
 if(!track14)return .5;
 const curve=track14.emotion17??(track14.emotion17=chooseEmotionV18(track14));
 const u=Math.max(0,Math.min(1,(bar-track14.start)/Math.max(1,track14.end-track14.start-1)))*6;
 const i=Math.min(5,Math.floor(u));return curve[i]+(curve[i+1]-curve[i])*(u-i);
}
function sectionRhythmV17(bar,meter){
 const sec=songSectionAt(bar),total=METER_BEATS[meter],units=Math.round(total*4);
 const patterns={
 'イントロ':[[2,2,4,2,2,4],[4,2,2,4,4]],
 'Aメロ':[[2,2,2,4,2,4],[4,2,2,2,2,4]],
 'Bメロ':[[4,2,2,3,3,2],[2,4,2,2,4,2]],
 'サビ':[[6,2,2,6],[2,6,4,4]],
 '間奏':[[2,2,4,4,2,2],[3,3,2,4,4]],
 'アウトロ':[[2,2,4,8],[4,4,8]]};
 const memory=track14.rhythm17??(track14.rhythm17=new Map());
 if(!memory.has(sec.name))memory.set(sec.name,pick(patterns[sec.name]||patterns['Aメロ']).slice());
 let weights=memory.get(sec.name).slice();
 // Answer bars vary the motif, rather than replacing it with unrelated rhythm.
 if(sec.offset%4===1)weights=[...weights.slice(1),weights[0]];
 if(sec.offset%4===3){const a=weights.pop(),b=weights.pop();weights.push(a+b);}
 if(sec.offset===sec.bars-1&&sec.name==='アウトロ')return [total];
 while(weights.length>units)weights.splice(-2,2,weights.at(-2)+weights.at(-1));
 let pos=0,raw=0;return weights.map((w,i)=>{raw+=w;const end=i===weights.length-1?units:Math.max(pos+1,Math.min(units-(weights.length-i-1),Math.round(raw*units/16)));const d=(end-pos)/4;pos=end;return d;});
}
function phraseTension(bar){
 const sec=songSectionAt(bar),p=sec.offset%8;
 const rising=[.16,.28,.39,.55,.42,.60,.78,.91][p];
 return Math.min(1,((track14?emotionV17(bar)*.65+rising*.25+sec.energy*.10:rising*.7+sec.energy*.3))*(.86+.14*personalityAt(bar).complexity));
}
function grooveAccent(bar,beat){const positions=grooveAt(bar);return positions.some(v=>Math.abs(v-beat)<.19)?1:0;}
function instrumentRole(inst){const name=(inst?.name||'').toLowerCase(),category=(inst?.category||'').toLowerCase();
 if(/bass|ベース|contrabass|コントラバス/.test(name))return 'bass';
 if(/guitar|ギター|harp|ハープ/.test(name))return 'plucked';
 if(/violin|viola|cello|string|ヴァイオリン|ビオラ|チェロ|ストリング/.test(name+category))return 'sustain';
 if(/flute|clarinet|oboe|sax|trumpet|フルート|クラリネット|オーボエ|サックス|トランペット/.test(name))return 'wind';
 return 'keys';
}
function melodyFitness(notes,rhythm,harmony,key){
 let score=0;
 for(let i=0;i<notes.length;i++){
  const n=notes[i],r=rhythm?.[i],ch=harmony?.[i],prev=notes[i-1];
  if(prev!==undefined){const d=Math.abs(n-prev);score+=d>9?-5:d>6?-2:d<=4?1.1:.2;if(i>1&&n===notes[i-2]&&n===prev)score-=1.5;}
  if(ch){const strong=!r||r.beatPosition<.05;score+=ch.notes?.has(n%12)?(strong?2:.6):(strong?-1.5:0);}
  if(r?.phraseEnd){const tonic=(n-key+120)%12;score+=[0,3,4,7].includes(tonic)?2:-1.2;}
 }
 return score;
}

let previousMelodyEnding=null;let previousMusicalKey=null,previousMusicalScale=null,musicalKeyBlock=-1,musicalScaleBlock=-1; let songMeasure=0, songHarmony=null, songSection=0, songMotif=null;
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
async function loadSoundBank(){if(loadingPromise)return loadingPromise;loadingPromise=(async()=>{setLoadProgress(1,'音源の読み込みを準備中…');const Ctx=window.AudioContext||window.webkitAudioContext;if(!Ctx)throw new Error('このブラウザはWeb Audio APIに対応していません');audioContext=new Ctx({latencyHint:'interactive'});const workletURL='https://cdn.jsdelivr.net/npm/spessasynth_lib@4.4.0/dist/spessasynth_processor.min.js';setLoadProgress(3,'音源エンジンを準備中…');await audioContext.audioWorklet.addModule(workletURL);synth=new WorkletSynthesizer(audioContext);mixAnalyser=audioContext.createAnalyser();mixAnalyser.fftSize=2048;mixSamples=new Float32Array(2048);mixGain=audioContext.createGain();synth.connect(mixAnalyser);mixAnalyser.connect(mixGain);mixGain.connect(audioContext.destination);await synth.isReady;setupChannelMetersV11();const compressed=await fetchWithProgress('./assets/GeneralUser-GS.sf2.gz');setLoadProgress(78,'SoundFontを展開中…');if(!('DecompressionStream'in window))throw new Error('このブラウザはgzip展開に対応していません');const stream=new Blob([compressed]).stream().pipeThrough(new DecompressionStream('gzip'));const bank=await new Response(stream).arrayBuffer();setLoadProgress(86,'261プリセットを含むSoundFontを登録中…');await synth.soundBankManager.addSoundBank(bank,'GeneralUser-GS');try{synth.controllerChange(0,0,0);synth.controllerChange(0,32,0);synth.programChange(0,0);}catch(_){}setLoadProgress(100,'音源：GeneralUser GS 読み込み完了');soundLoaded=true;el.start.disabled=false;setTimeout(()=>document.querySelector('.loading-area')?.classList.add('hidden'),1200);return true;})();return loadingPromise;}
// Multi-part arrangement: one MIDI channel per independently selected instrument.
const ARRANGEMENT_CHANNELS={leadLayer1:2,leadLayer2:3,backingLayer1:4,backingLayer2:5};
const arrangementActive=new Map();
function arrangementInstrument(id,fallback=null){const value=$(id)?.value;if(!value||value==='none')return null;if(value==='auto')return fallback;return instrumentById.get(value)||null;}
function setChannelInstrument(channel,inst){if(!synth||!inst)return;synth.controllerChange(channel,0,inst.bank);synth.controllerChange(channel,32,0);synth.programChange(channel,inst.program);synth.controllerChange(channel,7,110);
 try{synth.controllerChange(channel,91,Math.round(18+songIdentity(playbackBar).room*90));}catch(_){} }
function arrangementPitch(inst,pitch){if(!inst)return null;let n=pitch;while(n<inst.range[0])n+=12;while(n>inst.range[1])n-=12;return n>=inst.range[0]&&n<=inst.range[1]?n:null;}
function clearArrangementChannel(channel){for(const n of arrangementActive.get(channel)||[])try{synth?.noteOff(channel,n);}catch(_){}arrangementActive.set(channel,[]);}
function clearArrangement(preserveBasic=false){cancelArrangementEvents();for(const channel of Object.values(ARRANGEMENT_CHANNELS))clearArrangementChannel(channel);if(!preserveBasic){resetBacking19();try{synth?.controllerChange(1,123,0);}catch(_){}}}
function playArrangementPart(id,inst,pitches,velocity){if(!inst||!synth)return;const channel=ARRANGEMENT_CHANNELS[id];clearArrangementChannel(channel);const notes=[...new Set(pitches.map(n=>arrangementPitch(inst,n)).filter(n=>n!==null))];for(const n of notes)synth.noteOn(channel,n,velocity);arrangementActive.set(channel,notes);}
// Each added instrument follows its own repeating rhythmic motif. Timers are
// independent of lead-note timing, but are cancelled on stop or question end.
const arrangementTimers=new Set();
function cancelArrangementEvents(){for(const id of arrangementTimers)clearTimeout(id);arrangementTimers.clear();}
function arrangementEvent(delay,token,callback){
 // Use an absolute monotonic deadline, correcting timer drift while visible.
 // SpessaSynth's immediate note API still requires a JS callback; this is not sample-accurate scheduling.
 const clock=audioContext&&audioContext.state==='running'?()=>audioContext.currentTime*1000:()=>performance.now();
 const deadline=clock()+Math.max(0,delay);
 let id=null;
 const tick=()=>{
  arrangementTimers.delete(id);
  if(token!==runToken||!playing||!synth)return;
  const remaining=deadline-clock();
  if(remaining>7){id=setTimeout(tick,Math.max(1,remaining-3));arrangementTimers.add(id);return;}
  callback();
 };
 id=setTimeout(tick,Math.max(0,delay-4));arrangementTimers.add(id);
}
function playArrangementEvent(id,inst,pitches,velocity,holdMs,token,delayMs=0){
 arrangementEvent(delayMs,token,()=>{
  playArrangementPart(id,inst,pitches,velocity);
  arrangementEvent(holdMs,token,()=>clearArrangementChannel(ARRANGEMENT_CHANNELS[id]));
 });
}
function nearestChordTone(pcs,target,inst){
 if(!pcs?.length)return arrangementPitch(inst,target);
 const candidates=[];
 for(let n=inst.range[0];n<=inst.range[1];n++)if(pcs.includes(n%12))candidates.push(n);
 return candidates.length?candidates.reduce((a,b)=>Math.abs(a-target)<=Math.abs(b-target)?a:b):arrangementPitch(inst,target);
}
function arrangeIndependentParts(m,i,beatMs,slotMs,token,leadLayers,backingLayers,backing,collector=null){
 const emit=(id,inst,pitches,velocity,hold,delay=0)=>collector?collector.push({id,inst,pitches:[...pitches],velocity,holdMs:hold,delayMs:delay}):playArrangementEvent(id,inst,pitches,velocity,hold,token,delay);
 const silence=(id)=>{if(!collector)clearArrangementChannel(ARRANGEMENT_CHANNELS[id]);};
 const rhythm=m.rhythm?.[i],chord=m.harmony?.[i];
 const note=m.notes[i],measure=rhythm?.measure??Math.floor(i/4);
 const beat=rhythm?.beatPosition??(i%4),section=rhythm?.section??0;
 const phraseEnd=!!rhythm?.phraseEnd;
 const ending=songEnding(measure);
 const energy=musicalEnergy(measure),phrase=songSectionAt(measure);
 const sparse=musicGoal()==='song'&&energy<0.5;
 const phraseSlot=(measure%4)*4+Math.floor(beat);
 const phraseMotif=phrase.name+':'+phraseSlot;
 if(!songArrangementMotifs.has(phraseMotif))songArrangementMotifs.set(phraseMotif,Math.random());if(songArrangementMotifs.size>160)songArrangementMotifs.delete(songArrangementMotifs.keys().next().value);
 const motifGate=songArrangementMotifs.get(phraseMotif);
 const patternKey=songPersonalityGeneration+':'+phrase.name+':'+Math.floor(phrase.offset/4)%2;
 if(!arrangementMotifPatterns.has(patternKey))arrangementMotifPatterns.set(patternKey,[Math.random(),Math.random(),Math.random(),Math.random()]);
 const pattern=arrangementMotifPatterns.get(patternKey);
 const patternAccent=pattern[Math.floor(beat)%4]??.5;
 // The same phrase-level motif is reused with a small variation in the B section.
 const motif=(measure+Math.floor(beat))%4;
 const accent=grooveAccent(measure,beat),tension=phraseTension(measure),personality=personalityAt(measure);
 const activity=personality.density*(phrase.name==='サビ'?1.15:1);
 const phraseAnswer=phrase.offset%8>=4;
 const breakBar=musicGoal()==='song'&&phrase.offset%8===7&&beat>=2&&phrase.name!=='サビ';
 const arrangedRest=expressiveRest(rhythm,measure,'backing');
 for(const [id,inst] of leadLayers){
  if(!songPartEnabled(id,measure)||ending){silence(id);continue;}
  if(id==='leadLayer1'){
   // Sustained answer line: enters after the main melody on alternating beats,
   // leaving space on strong beats and at the beginning of phrases.
   const nextLead=m.notes[Math.min(i+1,m.notes.length-1)];
   const leadBusy=Math.abs(nextLead-note)>3&&rhythm?.beats<=0.5;
   const respond=((section===1?motif%3!==0:motif===1||motif===3)||phraseEnd)&&!leadBusy&&!breakBar&&(activity>0.9||motifGate<activity*.68)&&patternAccent<.9; 
   if(!respond||(sparse&&motifGate>0.46)){silence(id);continue;}
   const role=instrumentRole(inst);
   const target=note+(role==='wind'?7:note>65?-12:12);
   const pitch=nearestChordTone(chord?.pcs,target,inst);
   if(pitch!==null)emit(id,inst,[pitch],54,Math.max(90,slotMs*(instrumentRole(inst)==='sustain'?1.35:.7)),Math.min(slotMs*.25,beatMs*.25));
  }else{
   // Countermelody: answer in the gaps of the lead, with stepwise movement
   // around a chord tone and an independent offbeat rhythm.
   const next=m.notes[Math.min(i+1,m.notes.length-1)];
   const leadDirection=Math.sign(next-note);
   const target=Math.round((note+next)/2)-5+(section===1?2:0)-leadDirection*(phraseAnswer?4:2);
   const pitch=nearestChordTone(chord?.pcs,target,inst);
   if(pitch===null)continue;
   const entries=breakBar?[]:phraseEnd?[0]:sparse?[.55]:instrumentRole(inst)==='wind'?[.4]:motif%2===0?[.45]:activity>1&&phraseAnswer?[.15,.65]:[.4];
   for(const fraction of entries){
    const delay=slotMs*fraction;
    const second=nearestChordTone(chord?.pcs,pitch+(fraction>.5?2:0),inst);
    emit(id,inst,[second],42,Math.max(65,Math.min(beatMs*.38,slotMs*(1-fraction)*.8)),delay);
   }
  }
 }
 if(!m.accompanied||!chord||breakBar||arrangedRest)return;
 for(const [id,inst] of backingLayers){
  if(!songPartEnabled(id,measure)||ending){silence(id);continue;}
  const notes=enhancedVoicing(chord,note,inst,arrangementVoicing.get(id),measure);
  if(notes.length)arrangementVoicing.set(id,notes);
  if(!notes.length)continue;
  if(id==='backingLayer1'){
   // Bass plays roots on downbeats and occasional fifths on pickup beats.
   const root=nearestChordTone([chord.pcs[chord.inversion]??chord.root],Math.min(...notes)-12,inst);
   const fifth=nearestChordTone(chord.pcs,root+7,inst);
   // Retain a coherent bass contour over each four-bar phrase, with passing notes.
   const bassKey=songPersonalityGeneration+':'+phrase.name+':'+Math.floor(phrase.offset/4)%2;
   if(!songBassContour.has(bassKey))songBassContour.set(bassKey,[0,7,2,5].map(x=>x));
   const bassShape=songBassContour.get(bassKey);
   const bassTarget=nearestChordTone(chord.pcs,root+(bassShape[measure%4]===7?7:bassShape[measure%4]===5?-7:0),inst);
   const bassNotes=energy*activity>0.75&&slotMs>beatMs*.8?[root,bassTarget]:[root];
   bassNotes.forEach((n,j)=>emit(id,inst,[n],performanceVelocity(50,measure,beat,'bass'),Math.max(85,Math.min(beatMs*.78,slotMs/bassNotes.length*.8)),j*slotMs/bassNotes.length));
   // Walking/pickup approach into the next harmony only near a bar boundary.
   const nextChord=m.harmony?.[i+1];
   if(energy>0.62&&rhythm&&nextChord&&nextChord.harmonicStep!==chord.harmonicStep&&rhythm.beatPosition>=2&&slotMs>beatMs*.65){
     const nextRoot=nearestChordTone([nextChord.root],root,inst);
     const approach=arrangementPitch(inst,nextRoot+(nextRoot>root?-1:1));
     if(approach!==null)emit(id,inst,[approach],45,Math.min(beatMs*.2,110),Math.max(0,slotMs-beatMs*.25));
   }
  }else{
   // A separate broken-chord / syncopated pad rhythm; no unison doubling.
   const ordered=[...notes].sort((a,b)=>a-b);
   const role=instrumentRole(inst);
   const offsets=role==='sustain'?[0]:role==='wind'?(accent?[.5]:[.25]):role==='plucked'?(sparse?[0,.5]:activity>1?[0,.25,.5,.75]:[0,.5]):sparse?[0]:energy>0.75?(accent?[0,.33,.7]:[.25,.75]):motif%2===0?[0,.5]:[.25,.75];
   // The phrase pattern recurs, with occasional deliberate silence.
   const voicedOffsets=patternAccent>.82&&energy<.75?offsets.slice(0,1):offsets;
   if(patternAccent<.14&&beat>0&&!phraseEnd)continue;
   voicedOffsets.forEach((f,j)=>{
    const pitch=ordered[(j+motif)%ordered.length];
    emit(id,inst,[pitch],performanceVelocity(34+energy*12,measure,beat,'backing'),Math.max(75,Math.min(beatMs*.42,slotMs*(1-f)*.7)),slotMs*f);
   });
  }
 }
}
function updateArrangementVolumes(){if(!synth)return;for(const [id,ch] of Object.entries(ARRANGEMENT_CHANNELS))synth.controllerChange(ch,11,expressionV11(ch,mixLevel(id.startsWith('lead')?'melodyVolume':'accompanimentVolume')));}
function populateArrangementInstruments(){for(const id of ['leadInstrument','backingInstrument','leadLayer1','leadLayer2','backingLayer1','backingLayer2']){const select=$(id);if(!select)continue;const chordOnly=id.startsWith('backing');for(const inst of INSTRUMENTS){if(chordOnly&&!chordEligible(inst))continue;select.add(new Option(inst.name,inst.id));}}}
function selectPreset(inst){if(!synth)throw new Error('音源エンジンが準備できていません');synth.controllerChange(0,0,inst.bank);synth.controllerChange(0,32,0);synth.programChange(0,inst.program);synth.controllerChange(0,7,110);try{if(el.mode.value==='4')synth.controllerChange(0,91,Math.round(18+songIdentity(playbackBar).room*90));}catch(_){}if(el.mode.value==='4')applyMelodyExpression();else synth.controllerChange(0,11,127);}
function mixLevel(id){const n=Number(el[id]?.value);return Number.isFinite(n)?Math.max(0,Math.min(100,n)):80;}
function applyMelodyExpression(){
 if(!synth||el.mode.value!=='4')return;
 // MIDI expression CC11 persists for sustained notes, while note velocity
 // applies the chosen level to every newly started note.
 synth.controllerChange(0,11,expressionV11(0,mixLevel('melodyVolume')));
 synth.controllerChange(1,11,expressionV11(1,mixLevel('accompanimentVolume')));updateArrangementVolumes();
}
function updateMelodyMix(){applyMelodyExpression();}
let currentMelodyEnergy=0.65;
function melodyVelocity(){return Math.max(48,Math.min(115,Math.round(68+currentMelodyEnergy*39+(Math.random()-.5)*5)));}
function accompanimentVelocity(base){return Math.max(1,Math.min(127,base));}
for(const [id,label] of [['melodyVolume','melodyVolumeValue'],['accompanimentVolume','accompanimentVolumeValue']]){
 const slider=$(id),output=$(label);
 slider.addEventListener('input',()=>{output.value=slider.value+'%';output.textContent=slider.value+'%';updateMelodyMix();});
}
function noteOn(note,velocityOffset=0){synth.noteOn(0,note,Math.max(1,Math.min(127,melodyVelocity()+velocityOffset)));activeNotes.push(note);}
function noteOff(note){try{synth.noteOff(0,note);}catch(_){}activeNotes=activeNotes.filter(x=>x!==note);}
function stopAllNotes(){for(const n of [...activeNotes])noteOff(n);activeNotes=[];}
function setDisplayLines(lines,instrument,status,kind='normal'){el.answer.replaceChildren();el.answer.className='answer-'+kind;for(let i=0;i<lines.length;i++){const div=document.createElement('div');div.className=`answer-line answer-line-${i}`;div.textContent=lines[i];el.answer.append(div);}el.instrumentLabel.textContent='楽器：'+(instrument?.name||'—');el.status.textContent=status||'再生中';}
// A progression title names a known pattern and, where applicable, its harmonic technique.
// Do not infer chromaticism from the scale or add misleading "diatonic" labels.
function musicalProgressionLabel(name){
 const raw=String(name||'').trim();
 if(!raw||raw==='ダイアトニック進行'||raw==='音階構成音による和声'||raw==='自動生成')return '名称未設定の進行';
 const techniques=[
  [/セカンダリードミナント|V\/ii|V\/V|属七の連鎖|ドミナントの連鎖|III7–VI7–II7–V7/, 'セカンダリードミナント'],
  [/バックドア/, 'バックドア進行'],
  [/借用和音|マイナーサブドミナント|iv–I/, '借用和音'],
  [/クリシェ/, 'クリシェ'],
  [/sus4/, 'サスペンションの解決'],
  [/♭VI|♭VII/, 'モーダルインターチェンジ'],
  [/ii–V|ツーファイブ/, 'ii–V進行'],
 ];
 const match=techniques.find(([re])=>re.test(raw));
 if(!match||raw===match[1]||raw.includes('（'+match[1]+'）'))return raw;
 return raw+'（'+match[1]+'）';
}
// Always describe the ACTUAL chords played, including partial named phrases.
// A name alone can be misleading if a phrase branches before completion.
function progressionWithDegrees(name,items){
 const label=musicalProgressionLabel(name);
 const degrees=(items||[]).map(c=>String(c?.degree||'').trim()).filter(Boolean);
 const actual=degrees.join(' → ');
 if(!actual)return label;
 return label==='名称未設定の進行'?'度数進行：'+actual:label+'｜この区間：'+actual;
}
function setProgressionDisplay(keyText,name,chords,active,instrument,status){
 el.answer.className='answer-sequence answer-progression';
 let panel=el.answer.querySelector('.melody-harmony-panel');
 if(!panel){
  el.answer.replaceChildren();
  const heading=document.createElement('div');heading.className='sequence-heading';heading.textContent=keyText;el.answer.append(heading);
  panel=document.createElement('section');panel.className='melody-harmony-panel';
  const group=document.createElement('div');group.className='melody-progression-group';
  const title=document.createElement('div');title.className='melody-progression-title';
  title.textContent=progressionWithDegrees(name,chords);group.append(title);
  const grid=document.createElement('div');grid.className='melody-progression-chords';
  chords.forEach((chord,i)=>{
   const card=document.createElement('div');card.className='progression-item';card.dataset.progressionIndex=String(i);
   const number=document.createElement('div');number.className='progression-bar';number.textContent=(i+1)+'番目';
   const label=document.createElement('div');label.className='progression-chord';label.textContent=chordLabel(chord);
   const degree=document.createElement('div');degree.className='progression-degree';degree.textContent=chord.degree||'';
   card.append(number,label,degree);grid.append(card);
  });group.append(grid);panel.append(group);el.answer.append(panel);
 }
 for(const card of panel.querySelectorAll('.progression-item'))card.classList.toggle('progression-active',Number(card.dataset.progressionIndex)===active);
 el.instrumentLabel.textContent='楽器：'+instrument.name;el.status.textContent=status;
}
function setSequenceDisplay(title,notes,active,instrument,status,extra=''){el.answer.replaceChildren();el.answer.className='answer-sequence';const heading=document.createElement('div');heading.className='sequence-heading';heading.textContent=title;el.answer.append(heading);const row=document.createElement('div');row.className='sequence-notes';notes.forEach((n,i)=>{const span=document.createElement('span');span.textContent=noteName(n);span.className=i===active?'active-melody-note':'melody-note';row.append(span);if(i<notes.length-1)row.append(document.createTextNode(' → '));});el.answer.append(row);if(extra){const sub=document.createElement('div');sub.className='sequence-sub';sub.textContent=extra;el.answer.append(sub);}el.instrumentLabel.textContent='楽器：'+instrument.name;el.status.textContent=status;}
function setChordDisplay(chord,instrument,active=-1,status='コード再生中'){el.answer.replaceChildren();el.answer.className='answer-chord';const head=document.createElement('div');head.className='sequence-heading';head.textContent=chordLabel(chord)+' / '+(D.INVERSION_NAMES[chord.inversion]||'基本形');el.answer.append(head);const row=document.createElement('div');row.className='sequence-notes';chord.notes.forEach((n,i)=>{const span=document.createElement('span');span.textContent=noteName(n);span.className=(active===-1||active===i)?'active-melody-note':'melody-note';row.append(span);if(i<chord.notes.length-1)row.append(document.createTextNode(' - '));});el.answer.append(row);if(chord.frets){const f=document.createElement('div');f.className='sequence-sub';f.textContent='フォーム（6弦→1弦）：'+chord.frets.map(x=>x===null?'×':x).join('-');el.answer.append(f);}el.instrumentLabel.textContent='楽器：'+instrument.name;el.status.textContent=status;}
function speechEnabled(mode,part){return el.speech.value==='on'&&!!$(`speech-${mode}-${part}`)?.checked;}
function speechLang(mode,part){return $(`speech-lang-${mode}-${part}`)?.value==='en'?'en-US':'ja-JP';}
function pitchText(pitch,lang){if(lang==='en-US')return D.ENGLISH_SPEECH_NAMES[pitch];return D.JAPANESE_SPEECH_NAMES[pitch];}
async function speakPitch(pitch,lang){if(lang==='en-US'&&[4,5,9].includes(pitch)){await speak(({4:'イー',5:'エフ',9:'エー'})[pitch],'ja-JP');}else await speak(pitchText(pitch,lang),lang);}
function noteSpeech(note,mode){const lang=speechLang(mode,'notes'),pitch=note%12,oct=Math.floor(note/12)-1;return {text:pitchText(pitch,lang),lang,octave:$(`speech-octave-${mode}`)?.checked?String(oct):null};}
function speak(text,lang='ja-JP'){if(el.speech.value!=='on'||!text)return Promise.resolve();if(!('speechSynthesis'in window)||!('SpeechSynthesisUtterance'in window))return Promise.resolve();return new Promise(resolve=>{const u=new SpeechSynthesisUtterance(text);u.lang=lang;u.rate=Number(el.speed.value);u.volume=Number(el.speechVolume.value)/100;let done=false;let watchdog;const finish=()=>{if(done)return;done=true;clearTimeout(watchdog);resolve();};u.onend=finish;u.onerror=finish;watchdog=setTimeout(()=>{try{speechSynthesis.cancel();}catch(_){}finish();},20000);try{speechSynthesis.resume();speechSynthesis.speak(u);}catch(_){finish();}});}
async function speakPart(mode,part,text){if(speechEnabled(mode,part))await speak(text,speechLang(mode,part));}
async function speakInstrument(inst,mode){const ja=inst.nameJa||inst.name;const isJapanese=/[ぁ-んァ-ヶ一-龠]/.test(ja||'');const name=isJapanese?ja:(inst.presetName||inst.name||ja);await speakPart(mode,'instrument',name);}
async function speakNotes(notes,mode){if(!speechEnabled(mode,'notes'))return;for(const n of notes){const spec=noteSpeech(n,mode);const gap=Number(el.octaveGap.value);if(spec.octave!==null&&gap===0){ // One utterance avoids an artificial pause between pitch and octave.
 const pitch=n%12;const combined=spec.lang==='en-US'?`${D.ENGLISH_SPEECH_NAMES[pitch]} ${D.OCTAVE_ENGLISH?.[spec.octave]||spec.octave}`:`${spec.text} ${D.OCTAVE_ENGLISH?.[spec.octave]||spec.octave}`;
 await speak(combined,spec.lang);
 }else{await speakPitch(n%12,spec.lang);if(spec.octave!==null){await sleep(gap*1000);await speak(spec.octave,'en-US');}}}}

function intervalName(semitones,lang){const ja=(D.INTERVALS[String(semitones)]||`${semitones}半音`).replace(/^短/,'たん').replace(/^長/,'ちょう').replace(/^完全/,'かんぜん').replace(/^増/,'ぞう').replace(/^減/,'げん').replace(/度/g,'ど').replace(/2/g,'に').replace(/3/g,'さん').replace(/4/g,'よん').replace(/5/g,'ご').replace(/6/g,'ろく').replace(/7/g,'なな').replace(/8/g,'はち');const en={1:'minor second',2:'major second',3:'minor third',4:'major third',5:'perfect fourth',6:'tritone',7:'perfect fifth',8:'minor sixth',9:'major sixth',10:'minor seventh',11:'major seventh',12:'perfect octave'}[semitones]||`${semitones} semitones`;return lang==='en-US'?en:ja;}
function chordLabel(chord){const label=D.NAMES[chord.root%12]+(D.CHORD_DISPLAY_NAMES[chord.name]||chord.name);return chord.inversion>0&&chord.notes?.length?label+'/'+D.NAMES[chord.notes[0]%12]:label;}
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
// A phrase-aware, range-limited melody generator. Other modes are untouched.
function weightedChoice(items, weight){
  let total=0;const weights=items.map(x=>{const w=Math.max(0.0001,weight(x));total+=w;return w;});
  let r=Math.random()*total;
  for(let i=0;i<items.length;i++){r-=weights[i];if(r<=0)return items[i];}
  return items[items.length-1];
}
// Structured melody: repeating motifs, a calm verse, an active section, and a return.
// Meter is selected once per 16-bar block; a question is just an excerpt of the song.
let songMeter='4/4', songMeterBlock=-1, songRhythmCarry=null;
const METER_BEATS={'4/4':4,'3/4':3,'2/4':2,'6/8':3,'5/4':5};
const METER_GROUPS={'4/4':[2,2],'3/4':[3],'2/4':[2],'6/8':[1.5,1.5],'5/4':[3,2]};
function meterAtBar(bar){
 if(track14)return track14.meter;
  const mode=el.melodyMeter?.value||'4/4';
  if(mode!=='random'){songMeter=mode;songMeterBlock=Math.floor(bar/16);return mode;}
  const block=Math.floor(bar/(musicGoal()==='song'?SONG_FORM_LENGTH:16));
  if(block!==songMeterBlock){songMeterBlock=block;songMeter=pick(['4/4','4/4','3/4','6/8','2/4','5/4']);}
  return songMeter;
}
function rhythmPattern(meter,section,phrasePosition){
  const total=METER_BEATS[meter];
  const groups=METER_GROUPS[meter];
  // Keep a recognisable pulse. Small notes are embellishments, not the backbone.
  if(phrasePosition===3)return [total];
  if(phrasePosition===2&&songMotif?.meter===meter)return songMotif.beats.slice();
  let beats=[];
  if(section===0){
    beats=pick([groups.slice(),[total/2,total/2],[total],
      total>=3?[1,1,total-2]:[1,total-1]]).filter(x=>x>0);
  }else{
    beats=pick([groups.slice(),[total/2,total/2],
      total>=3?[0.5,0.5,1,total-2]:[0.5,0.5,total-1],
      total>=3?[1,0.5,0.5,total-2]:[1,total-1]]).filter(x=>x>0);
  }
  if(section===1&&Math.random()<0.035){
    const index=beats.findIndex(x=>x>=1);
    if(index>=0){const value=beats[index];beats.splice(index,1,1/3,1/3,1/3,...(value>1?[value-1]:[]));}
  }else if(section===1&&Math.random()<0.035){
    const index=beats.findIndex(x=>x>=1);
    if(index>=0){const value=beats[index];beats.splice(index,1,0.25,0.25,0.5,...(value>1?[value-1]:[]));}
  }
  if(phrasePosition===0)songMotif={meter,beats:beats.slice()};
  return beats;
}
function melodicRhythm(count){
  const result=[];let bar=songRhythmCarry?.bar??songMeasure,position=songRhythmCarry?.position??0,pattern=songRhythmCarry?.pattern?.slice()??[],idx=songRhythmCarry?.idx??0;
  // Complete a bar before beginning the next question: songMeasure is a bar cursor.
  while(result.length<count&&(!track14||bar<track14.end)){
    const meter=meterAtBar(bar),total=METER_BEATS[meter];
    const section=(musicalEnergy(bar)*personalityAt(bar).density)>=0.65?1:0;
    if(idx>=pattern.length){pattern=track14&&musicGoal()==='song'?sectionRhythmV17(bar,meter):rhythmPattern(meter,section,bar%4);idx=0;position=0;}
    const beats=pattern[idx++];
    const endOfBar=position+beats>=total-1e-6;
    const phraseEnd=endOfBar&&bar%4===3;
    // Most notes are connected. Detached accents and rests are uncommon.
    let articulation=section===1?0.94:0.98;
    if(Math.random()<(section===1?0.045:0.015))articulation=0.58;
    if(phraseEnd)articulation=0.99;
    const rest=track14?0:phraseEnd&&Math.random()<0.3?0.5:((bar%8===3&&position>=total-1&&Math.random()<.12)?0.25:0);
    result.push({beats,rest,articulation,phraseEnd,measure:bar,beatPosition:position,section,meter});
    position+=beats;
    if(endOfBar){bar++;idx=0;pattern=[];}
  }
  // Preserve unfinished bar position for next question by carrying remaining events.
  // Questions can end mid-bar, but the next question continues its rhythmic motif.
  if(idx<pattern.length){songRhythmCarry={bar,pattern:pattern.slice(),idx,position};}
  else songRhythmCarry=null;
  songMeasure=bar;
  return result;
}
// Progressions are defined in diatonic scale degrees. Variants introduce
// secondary dominants and borrowed chords only for familiar major/minor scales.
const SONG_PROGRESSIONS=[
 {name:'王道進行',degrees:[3,4,2,5],types:['maj7','7','m7','m7']},
 {name:'カノン進行',degrees:[0,4,5,2,3,0,3,4],types:['','', 'm','m','','','', '7']},
 {name:'I–V–vi–IV',degrees:[0,4,5,3],types:['','','m','']},
 {name:'ii–V–I–vi',degrees:[1,4,0,5],types:['m7','7','maj7','m7']},
 {name:'I–vi–ii–V',degrees:[0,5,1,4],types:['maj7','m7','m7','7']},
 {name:'IV–V–iii–vi',degrees:[3,4,2,5],types:['maj7','7','m7','m7']},
 {name:'ブルース風',degrees:[0,3,0,4],types:['7','7','7','7']},
 {name:'マイナー循環',degrees:[0,5,2,4],types:['m','','dim','7']},
 {name:'アンダルシア進行',degrees:[0,6,5,4],types:['m','','','7']},
 {name:'i–iv–VII–III',degrees:[0,3,6,2],types:['m','m','','']}
];
const CHORD_INTERVALS={'':[0,4,7],m:[0,3,7],dim:[0,3,6],aug:[0,4,8],sus4:[0,5,7],
 '7':[0,4,7,10],maj7:[0,4,7,11],m7:[0,3,7,10],m7b5:[0,3,6,10],dim7:[0,3,6,9],
 add9:[0,4,7,14],madd9:[0,3,7,14], '9':[0,4,7,10,14]};
// Progressions are reusable musical phrases, not mandatory sequences at question boundaries.
// Candidate transitions are scored by harmonic function and common tones.
function progressionEntries(p,key,degrees){
 const types={'Major':'','Minor':'m','Major7':'maj7','Minor7':'m7','7th':'7','HalfDim7':'m7b5','dim':'dim','aug':'aug','sus4':'sus4'};
 return (p.chords||p.degrees).map((entry,i)=>{
  const degree=p.chords?Math.min(6,Math.floor((entry[0]%12)/2)):entry%degrees.length;
  const root=p.chords?(key+entry[0])%12:degrees[degree];
  const triad=[0,2,4].map(x=>degrees[(degree+x)%degrees.length]);
  const relative=triad.map(pc=>(pc-root+12)%12);
  let quality=relative[1]===3&&relative[2]===7?'m':relative[1]===3&&relative[2]===6?'dim':relative[1]===4&&relative[2]===8?'aug':'';
  if(p.chords)quality=types[entry[1]]??quality;
  else quality=p.types?.[i]||quality;
  return {root,quality,degree,degreeLabel:p.chords?.[i]?.[2],pcs:[...new Set((CHORD_INTERVALS[quality]||CHORD_INTERVALS['']).map(x=>(root+x)%12))]};
 });
}
// Functional harmony, bass motion and smooth voice leading are evaluated together.
function pitchDistance(a,b){const d=Math.abs(a-b)%12;return Math.min(d,12-d);}
function harmonicRole(c,key){
 const degree=(c.root-key+12)%12;
 if(degree===0||degree===9)return 'tonic';
 if(degree===5||degree===2)return 'predominant';
 if(degree===7||degree===11||c.quality==='7')return 'dominant';
 return 'color';
}
function voiceLeadingCost(a,b){
 if(!a||!b)return 0;
 const one=a.pcs||[],two=b.pcs||[];
 if(!one.length||!two.length)return 0;
 const forward=one.reduce((sum,n)=>sum+Math.min(...two.map(m=>pitchDistance(n,m))),0)/one.length;
 const backward=two.reduce((sum,n)=>sum+Math.min(...one.map(m=>pitchDistance(n,m))),0)/two.length;
 return (forward+backward)/2;
}
function harmonicTransitionScore(previous,next,key,context={}){
 if(!previous)return 1;
 const prevRole=harmonicRole(previous,key),nextRole=harmonicRole(next,key);
 const motion=(next.root-previous.root+12)%12;
 const bassFrom=previous.pcs?.[previous.inversion||0]??previous.root;
 const bassTo=next.pcs?.[next.inversion||0]??next.root;
 const bassDistance=pitchDistance(bassFrom,bassTo);
 let score=Math.exp(-0.23*voiceLeadingCost(previous,next));
 // Tonic -> predominant -> dominant -> tonic; allow deceptive resolutions.
 const functionWeights={
  tonic:{tonic:0.8,predominant:1.8,dominant:1.15,color:0.9},
  predominant:{tonic:0.75,predominant:0.95,dominant:2.6,color:1.0},
  dominant:{tonic:3.8,predominant:0.55,dominant:0.85,color:1.15},
  color:{tonic:1.5,predominant:1.35,dominant:1.25,color:0.8}
 };
 score*=functionWeights[prevRole][nextRole];
 if(motion===5||motion===7)score*=1.45;
 if(motion===2||motion===10)score*=1.18;
 if(motion===0)score*=0.72;
 if(previous.quality==='7'&&motion===5)score*=2.3;
 score*=Math.exp(-0.085*bassDistance);
 // A melody's last note is a soft constraint, not a prohibition of suspensions.
 if(Number.isFinite(context.melodyPitch)){
  const pc=((context.melodyPitch%12)+12)%12;
  if(next.pcs.includes(pc))score*=1.35;
  else if(next.pcs.some(n=>pitchDistance(n,pc)<=2))score*=0.94;
  else score*=0.68;
 }
 if(context.cadence&&nextRole==='tonic'&&prevRole==='dominant')score*=1.65;
 return Math.max(0.02,score);
}
// One stylistic palette per continuous harmonic passage. J-POP and rock share
// common pop patterns; jazz-specific dominant chains stay in jazz passages.
const MELODY_GENRES=['J-POP','ロック','ジャズ'];
function songProgressionGenre(){
 return weightedChoice(MELODY_GENRES,g=>g==='J-POP'?55:g==='ロック'?30:15);
}
function progressionMood(p,key,degrees){
 const entries=progressionEntries(p,key,degrees);
 if(!entries.length)return 0;
 return entries.reduce((sum,c)=>sum+(c.quality.startsWith('m')||c.quality==='dim'?-1:c.quality==='7'?0.15:0.75),0)/entries.length;
}
function chordMood(c){return c&&(c.quality.startsWith('m')||c.quality==='dim')?-1:0.7;}
function chooseSongProgression(majorLike,minorLike,previous,lastChord,key,degrees,genre,mood=0,context={}){
 const standard=SONG_PROGRESSIONS.filter(p=>majorLike?!p.name.startsWith('マイナー')&&p.name!=='アンダルシア進行'&&p.name!=='i–iv–VII–III':minorLike?p.name.startsWith('マイナー')||p.name==='アンダルシア進行'||p.name==='i–iv–VII–III':false);
 const chromatic=THEORY_PROGRESSIONS.filter(p=>p.mode===(majorLike?'major':'minor')&&(p.genre===genre||p.genre==='マイナー'));
 const extended=EXTENDED_PROGRESSION_LIBRARY.filter(p=>p.mode===(majorLike?'major':'minor')&&(p.genre===genre||p.genre==='マイナー'));
 const stylistic=standard.filter(p=>{
  if(genre==='ジャズ')return /ii–V|I–vi|循環|ブルース|マイナー/.test(p.name);
  if(genre==='ロック')return /I–V–vi–IV|ブルース|カノン|マイナー|アンダルシア/.test(p.name);
  return !/ブルース|ii–V–I–vi|I–vi–ii–V/.test(p.name);
 });
 const all=[...stylistic,...extended,...chromatic];
 if(!all.length)return {name:'I–IV–V–I（基本進行）',degrees:[0,3,4,0],types:[]};
 return weightedChoice(all,p=>{
  let w=stylistic.includes(p)?4:extended.includes(p)?3:1.8;
  if(genre==='J-POP'&&/王道|カノン|借用|クリシェ/.test(p.name))w*=2.1;
  if(genre==='ロック'&&/I–V–vi–IV|ブルース|sus4|♭VI/.test(p.name))w*=2;
  if(genre==='ジャズ'&&/ii–V|循環|バックドア|セカンダリー/.test(p.name))w*=2.1;
  if(previous&&p.name===previous.name)w*=0.08;
  // Tonicization/borrowed colors are occasional, mostly in higher-tension sections.
  if(/セカンダリー|借用|バックドア|♭VI|♭VII/.test(p.name))w*=context.tension>.72?1.6:0.48;
  // Favor a consistent emotional palette; occasional contrasting color is intentional.
  const distance=Math.abs(progressionMood(p,key,degrees)-mood);
  w*=Math.random()<0.075?1:Math.exp(-1.7*distance);
  const entries=progressionEntries(p,key,degrees);
  const first=entries[0];
  // Score the phrase as a whole: prefer meaningful tension followed by release.
  let phraseScore=1;
  for(let i=1;i<entries.length;i++){
   const prev=entries[i-1],next=entries[i];
   const transition=harmonicTransitionScore(prev,next,key,{cadence:i===entries.length-1});
   phraseScore*=Math.pow(Math.max(0.1,Math.min(8,transition)),0.16/Math.max(1,entries.length-1));
  }
  const endRole=harmonicRole(entries.at(-1),key);
  if(endRole==='tonic')phraseScore*=context?.cadence?2.0:1.16;
  if(context?.halfCadence&&endRole==='dominant')phraseScore*=1.65;
  return w*phraseScore*harmonicTransitionScore(lastChord,first,key,context);
 });
}
function harmonicSlotForNote(r,measure,beats){
 const position=r?.beatPosition??0;
 const section=r?.section??0;
 // Keep the same harmonic rhythm within a bar, but vary the pattern across bars.
 // The selected positions are beat offsets; 6/8 and odd meters are handled in beats.
 const patterns=beats>=4?[
  {w:45,at:[0]}, {w:28,at:[0,beats/2]},
  {w:11,at:[0,beats*0.75]}, {w:8,at:[0,beats/4,beats/2]},
  {w:5,at:[0,beats/2,beats*0.75]}, {w:3,at:[0,beats/4,beats/2,beats*0.75]}
 ]:beats>=3?[
  {w:55,at:[0]}, {w:30,at:[0,Math.ceil(beats/2)]},
  {w:10,at:[0,1]}, {w:5,at:[0,1,2]}
 ]:[{w:70,at:[0]},{w:30,at:[0,1]}];
 if(!songHarmony.harmonicPatterns) songHarmony.harmonicPatterns=new Map();
 let pattern=songHarmony.harmonicPatterns.get(measure);
 if(!pattern){
  const chosen=weightedChoice(patterns,p=>p.w*(section===1?p.at.length:1));
  pattern=chosen.at;songHarmony.harmonicPatterns.set(measure,pattern);
 }
 // A chord can only change on an actual note onset. The closest previous
 // rhythmic boundary becomes the active slot; no phantom changes are shown.
 let slot=0;
 for(let j=1;j<pattern.length;j++)if(position>=pattern[j]-1e-5)slot=j;
 return slot;
}
function melodyHarmony(scale,key,count,rhythm){
 const degrees=D.SCALES[scale].map(x=>(key+x)%12);
 const majorLike=degrees.length===7&&[0,2,4,5,7,9,11].every(x=>D.SCALES[scale].includes(x));
 const minorLike=degrees.length===7&&[0,2,3,5,7,8,10].every(x=>D.SCALES[scale].includes(x));
 if(!songHarmony||songHarmony.key!==key||songHarmony.scale!==scale){
  songHarmony={key,scale,progression:null,progressionIndex:0,groupId:0,lastSlotId:null,cache:new Map(),harmonicPatterns:new Map(),previousProgression:null,lastChord:null,questionEnd:null,phraseChordCount:0,phraseTarget:0,genre:musicGoal()==='song'?personalityAt(rhythm?.[0]?.measure??songMeasure).genre:songProgressionGenre(),groupHistory:new Map(),mood:null,holdUntilBar:-1,lastChordStartBar:-1};
 }
 const h=songHarmony,result=[];
 const startBar=rhythm?.[0]?.measure??songMeasure;
 for(let i=0;i<count;i++){
  const r=rhythm?.[i],measure=r?.measure??startBar+Math.floor(i/4);
  const beats=METER_BEATS[r?.meter]||4;
  const slot=harmonicSlotForNote(r,measure,beats),slotId=measure+':'+slot;
  if(h.cache.has(slotId)){result.push(h.cache.get(slotId));continue;}
  // A sustained harmony can last two or three full bars, independent of question boundaries.
  // Reuse the same harmonic identity while retaining a separate visible slot.
  const held=h.lastChord&&measure<h.holdUntilBar;
  if(held){
   const chord={...h.lastChord,measure,slot};
   h.cache.set(slotId,chord);result.push(chord);
   const history=h.groupHistory.get(chord.groupId)||[];
   history.push(chordInfo(chord,key,scale,measure));h.groupHistory.set(chord.groupId,history);
   continue;
  }
  const atQuestionStart=i===0&&h.questionEnd!==null&&slotId!==h.questionEnd;
  const length=h.progression?(h.progression.chords?.length||h.progression.degrees.length):0;
  const finished=!h.progression||h.progressionIndex>=length;
  // Musical phrases can end *inside* a question. Prefer 2-4 chord phrases;
  // occasionally keep the full named pattern. A change is only made at a
  // real harmonic slot (not at each melody note).
  const phraseComplete=h.progression&&h.phraseChordCount>=h.phraseTarget;
  const branch=atQuestionStart&&!finished&&Math.random()<0.18*personalityAt(measure).complexity;
  const change=finished||branch||phraseComplete;
  if(change){
   const prior=h.progression;
   h.progression=chooseSongProgression(majorLike,minorLike,prior,h.lastChord,key,degrees,h.genre,h.mood??0,{melodyPitch:previousMelodyEnding,tension:phraseTension(measure),cadence:measure%8===7,halfCadence:measure%8===3});
   h.progressionIndex=0;h.groupId++;h.phraseChordCount=0;
   if(h.mood===null)h.mood=progressionMood(h.progression,key,degrees);
   const newLength=h.progression.chords?.length||h.progression.degrees.length;
   // Weights: 2 chords 20%, 3 chords 35%, 4 chords 30%, full phrase 15%.
   const choice=weightedChoice([{n:2,w:20},{n:3,w:35},{n:4,w:30},{n:newLength,w:15}],x=>x.w);
   h.phraseTarget=Math.min(newLength,musicGoal()==='song'&&musicalEnergy(measure)<0.55?Math.max(3,choice.n):choice.n);
  }
  const prog=h.progression,idx=h.progressionIndex++;h.phraseChordCount++;
  const info=progressionEntries(prog,key,degrees)[idx];
  const inversion=weightedChoice(Array.from({length:info.pcs.length},(_,n)=>n),n=>{
   const prevBass=h.lastChord?.pcs?.[h.lastChord.inversion||0];
   if(prevBass===undefined)return n===0?7:1;
   const distance=pitchDistance(prevBass,info.pcs[n]);
   return Math.exp(-0.32*distance)*(n===0?2.3:1);
  });
  const chord={...info,measure,slot,harmonicStep:h.groupId*1000+idx,inversion,
   notes:new Set(info.pcs),groupId:h.groupId,progressionName:prog.name,
   progressionPosition:idx+1,progressionLength:prog.chords?.length||prog.degrees.length};
  h.lastChord=chord;h.lastSlotId=slotId;
  // Strongly prefer one-bar harmonies; occasionally sustain for 2–3 bars.
  // Do not sustain at an internal mid-bar slot; this avoids erratic syncopated holds.
  if(slot===0){
   const hold=weightedChoice([{bars:1,w:82},{bars:2,w:15},{bars:3,w:3}],x=>x.w);
   h.holdUntilBar=measure+hold.bars;
  }else h.holdUntilBar=measure;
  h.mood=h.mood===null?chordMood(chord):h.mood*0.94+chordMood(chord)*0.06;
  h.cache.set(slotId,chord);result.push(chord);
  // Store the complete current phrase across question boundaries.
  const history=h.groupHistory.get(h.groupId)||[];
  history.push(chordInfo(chord,key,scale,measure));
  h.groupHistory.set(h.groupId,history);
  if(h.groupHistory.size>12)h.groupHistory.delete(h.groupHistory.keys().next().value);
  if(h.cache.size>256)h.cache.delete(h.cache.keys().next().value);
 }
 h.questionEnd=result.at(-1)?.measure+':'+result.at(-1)?.slot;
 if(h.harmonicPatterns.size>256)h.harmonicPatterns.delete(h.harmonicPatterns.keys().next().value);
 return result;
}
function accompanimentNotes(chord,melody,inst){
  if(!chord)return [];
  // Accompaniment may sit above a low melody, rather than disappearing below it.
  const min=inst.range[0],max=inst.range[1];
  const centers=[melody-12,melody+12,Math.round((min+max)/2)-6];
  const candidateSets=[];
  for(const center of centers){
    const pitches=[];
    for(const pc of chord.pcs){
      const possible=[];
      for(let n=min;n<=max;n++)if(n%12===pc)possible.push(n);
      if(possible.length)pitches.push(possible.reduce((a,b)=>Math.abs(a-center)<Math.abs(b-center)?a:b));
    }
    if(pitches.length===chord.pcs.length){
      const unique=[...new Set(pitches)].sort((a,b)=>a-b);
      if(unique.length===chord.pcs.length)candidateSets.push(unique);
    }
  }
  if(!candidateSets.length)return [];
  const desiredBass=chord.pcs[chord.inversion]??chord.root;
  const inverted=candidateSets.filter(arr=>arr[0]%12===desiredBass);
  const choices=inverted.length?inverted:candidateSets;
  return choices.sort((a,b)=>{
    const penalty=arr=>arr.reduce((v,n)=>v+Math.max(0,8-Math.abs(n-melody))*2,0)
      +Math.max(0,arr[arr.length-1]-arr[0]-16);
    return penalty(a)-penalty(b);
  })[0];
}
function setAccompanimentPreset(inst){
  // Channel 1 is reserved for accompaniment; channel 0 stays with the melody.
  synth.controllerChange(1,0,inst.bank);
  synth.controllerChange(1,32,0);
  synth.programChange(1,inst.program);
  synth.controllerChange(1,7,110);applyMelodyExpression();
}
const MUSICAL_SCALE_FAMILIES=[
  ['メジャー','アイオニアン','リディアン','ミクソリディアン'],
  ['ナチュラルマイナー','エオリアン','ドリアン','フリジアン','ハーモニックマイナー','メロディックマイナー'],
];
function musicalScaleDistance(a,b){
  const aa=new Set(D.SCALES[a]||[]),bb=new Set(D.SCALES[b]||[]);
  let common=0;for(const x of aa)if(bb.has(x))common++;
  return common/Math.max(1,Math.max(aa.size,bb.size));
}
function chooseMusicalScale(all){
  const block=Math.floor(songMeasure/(musicGoal()==='song'?SONG_FORM_LENGTH:16));
  if(previousMusicalScale&&musicalScaleBlock===block&&all.includes(previousMusicalScale))return previousMusicalScale;
  musicalScaleBlock=block;
  const candidates=all.filter(x=>Array.isArray(D.SCALES[x])&&D.SCALES[x].length>=5);
  if(!candidates.length)return pick(all);
  if(!previousMusicalScale||Math.random()<0.7){
    if(previousMusicalScale&&candidates.includes(previousMusicalScale))return previousMusicalScale;
    return pick(candidates);
  }
  return weightedChoice(candidates,x=>{
    if(x===previousMusicalScale)return 12;
    const sameFamily=MUSICAL_SCALE_FAMILIES.some(f=>f.includes(x)&&f.includes(previousMusicalScale));
    return (sameFamily?7:1)*Math.pow(Math.max(0.05,musicalScaleDistance(x,previousMusicalScale)),3);
  });
}
function chooseMusicalKey(scaleName){
  const block=Math.floor(songMeasure/(musicGoal()==='song'?SONG_FORM_LENGTH:16));
  if(previousMusicalKey!==null&&musicalKeyBlock===block)return previousMusicalKey;
  musicalKeyBlock=block;
  if(previousMusicalKey===null)return Math.floor(Math.random()*12);
  // A change is rare; fifth-related, relative and parallel relationships dominate.
  if(Math.random()<0.76)return previousMusicalKey;
  const candidates=[previousMusicalKey,(previousMusicalKey+7)%12,(previousMusicalKey+5)%12,(previousMusicalKey+9)%12,(previousMusicalKey+3)%12];
  return weightedChoice(candidates,k=>{
    if(k===previousMusicalKey)return 5;
    const prev=new Set((D.SCALES[previousMusicalScale]||D.SCALES[scaleName]).map(n=>(n+previousMusicalKey)%12));
    const next=(D.SCALES[scaleName]||[]).map(n=>(n+k)%12);
    return Math.pow(1+next.filter(n=>prev.has(n)).length,3);
  });
}
function chordInfo(chord,key,scale,measure){
 if(!chord)return null;
 const roman=['I','II','III','IV','V','VI','VII'][chord.degree%7];
 const lower=chord.quality.startsWith('m')||chord.quality.startsWith('dim');
 const degree=chord.degreeLabel||((lower?roman.toLowerCase():roman)+(chord.quality==='dim'?'°':''));
 const bass=chord.pcs[chord.inversion]??chord.root;
 const slash=chord.inversion?'/'+D.NAMES[bass]:'';
 return {root:chord.root,quality:chord.quality,degree,chord:chord.pcs,measure,inversion:chord.inversion,bass,
  name:D.NAMES[chord.root]+chord.quality+slash,slot:chord.slot??0,harmonicStep:chord.harmonicStep,groupId:chord.groupId,progressionName:chord.progressionName,progressionPosition:chord.progressionPosition,progressionLength:chord.progressionLength};
}
function displayMelodyChords(m,index){
 if(!m.harmony)return;
 const active=m.chordInfos?.[index];if(!active)return;
 let panel=el.answer.querySelector('.melody-harmony-panel');
 if(!panel){
  panel=document.createElement('section');panel.className='melody-harmony-panel';
  const heading=document.createElement('div');heading.className='sequence-heading';
  heading.textContent='この問題のコード進行';panel.append(heading);
  const seen=new Set(),groups=[];
  for(const c of m.chordInfos){
   if(!c)continue;
   const id=c.measure+':'+c.slot;
   if(seen.has(id))continue;seen.add(id);
   let group=groups.at(-1);
   if(!group||group.id!==c.groupId){group={id:c.groupId,name:c.progressionName,items:[]};groups.push(group);}
   if(!group.items.length){
    const history=songHarmony?.groupHistory?.get(c.groupId)||[];
    const firstCurrent=c.measure+':'+c.slot;
    for(const old of history){
     if(old.measure+':'+old.slot===firstCurrent)break;
     group.items.push({...old,previousQuestion:true});
    }
   }
   group.items.push(c);
  }
  for(const group of groups){
   const wrapper=document.createElement('div');wrapper.className='melody-progression-group';
   const title=document.createElement('div');title.className='melody-progression-title';
   const positions=new Set(group.items.map(c=>c.progressionPosition).filter(Number.isFinite));
   const total=group.items.find(c=>c.progressionLength)?.progressionLength||4;
   // Short excerpts do not substantiate a named progression. Require at least
   // three distinct positions and most of the pattern (all four for a 4-chord phrase).
   const required=total<=4?Math.min(total,4):Math.max(4,Math.ceil(total*0.65));
   const recognized=positions.size>=required;
   if(!recognized)wrapper.classList.add('melody-progression-fragment');
   title.textContent=(recognized?progressionWithDegrees(group.name,group.items):'和声のつながり：'+group.items.filter((c,i,a)=>i===0||c.progressionPosition!==a[i-1].progressionPosition).map(c=>c.degree).join(' → '))+(recognized?'（この枠の範囲）':'（進行名は未確定）');wrapper.append(title);
   const row=document.createElement('div');row.className='melody-progression-chords';
   for(const c of group.items){
    const item=document.createElement('div');item.className='progression-item';item.dataset.harmonyId=c.measure+':'+c.slot;if(c.previousQuestion)item.classList.add('previous-question-chord');
    const number=document.createElement('div');number.className='progression-bar';
    number.textContent=(c.previousQuestion?'前問・':'')+(c.measure+1)+'小節'+(c.slot?' / '+(c.slot+1)+'番目':' / 1番目');
    const name=document.createElement('div');name.className='progression-chord';name.textContent=c.name;
    const degree=document.createElement('div');degree.className='progression-degree';degree.textContent=c.degree;
    item.append(number,name,degree);row.append(item);
   }
   wrapper.append(row);panel.append(wrapper);
  }
  el.answer.append(panel);
 }
 const activeId=active.measure+':'+active.slot;
 for(const item of panel.querySelectorAll('.progression-item'))item.classList.toggle('progression-active',item.dataset.harmonyId===activeId);
}
function displayMelodyQuestion(m){
 setSequenceDisplay(`${D.NAMES[m.key]} / ${m.scaleName}`,m.notes,-1,m.inst,`メロディ再生準備 ${m.notes.length}音`);
 // The full chord progression is visible as soon as the question is generated.
 if(m.harmony)displayMelodyChords(m,0);
}
function updateMelodyQuestion(m,i,label){
 const notes=el.answer.querySelectorAll('.sequence-notes .melody-note, .sequence-notes .active-melody-note');
 notes.forEach((node,j)=>node.className=j===i?'active-melody-note':'melody-note');
 const sec=m.rhythm?.[i]?songSectionAt(m.rhythm[i].measure):null;
 el.status.textContent=`${track14?`第${track14.id}曲 / ${Math.round(track14.bpm)} BPM / `:''}${sec&&musicGoal()==='song'?sec.name+'・'+personalityAt(m.rhythm[i].measure).name+' / ':''}メロディ再生中 ${i+1}/${m.notes.length}${label}`;
 if(m.harmony)displayMelodyChords(m,i);
}
function accompanimentStyle(section){
  const mode=el.melodyAccompStyle?.value||'auto';
  return mode==='auto'?(section===1?'arpeggio':'block'):mode;
}
// Motifs are anchored to 4-bar phrases, not to question boundaries.
// A melody question is a window into a continuing song.
function melodicPhrasePlan(rhythm,scaleName,key){
 if(!rhythm)return null;
 const out=[];
 for(const r of rhythm){
  const bar=r.measure,phrase=Math.floor(bar/4),section=songSectionAt(bar);
  const identity=musicGoal()==='song'?(section.name==='サビ'?'chorus':section.name==='Aメロ'?'verse':section.name==='Bメロ'?'bridge':section.name):'practice-'+phrase;
  const motifKey=identity+':'+(bar%4);
  let motif=songMelodyMotifs.get(motifKey);
  if(!motif){
   const contour=[0,2,4,2,0,-1,1,0];
   motif=contour.map((v,i)=>v+(Math.random()<.15?(Math.random()<.5?-1:1):0));
   songMelodyMotifs.set(motifKey,motif);if(songMelodyMotifs.size>120) songMelodyMotifs.delete(songMelodyMotifs.keys().next().value);
  }
  const localIndex=Math.max(0,Math.round(r.beatPosition*2));
  const motifOffset=motif[localIndex%motif.length];
  const phraseEnd=r.phraseEnd;
  out.push({motifOffset,phraseEnd,section,energy:musicalEnergy(bar),variation:musicGoal()==='training'?0.4:0.08,themeKey:phraseIdentity(r),themeSlot:(bar%4)*8+Math.round(r.beatPosition*2),bar,beat:r.beatPosition});
 }
 return out;
}
function cadenceWeight(note,key,chord,r,phrasePlan){
 if(!r)return 1;
 const barEnd=r.phraseEnd,section=phrasePlan?.section;
 if(!barEnd)return 1;
 const relative=(note-key+120)%12;
 const tonic=relative===0,third=relative===3||relative===4,fifth=relative===7;
 const isHalf=section?.name==='Bメロ'||(section?.offset%8<4&&section?.name!=='アウトロ'&&section?.name!=='サビ');
 if(isHalf)return relative===7?4:chord?.notes?.has(note%12)?1.5:0.65;
 return tonic?5:third?2.5:fifth?1.8:0.45;
}
// V7: score complete candidate phrases instead of accepting every first draw.
// Keep the score balanced: over-penalizing leaps produces dull stepwise tunes.
function phraseCandidateScore(notes,rhythm,harmony,key){
 let score=melodyFitness(notes,rhythm,harmony,key);
 if(!notes.length)return score;
 const unique=new Set(notes.map(n=>n%12)).size;
 score+=Math.min(5,unique)*.8;
 let direction=0,turns=0,repeated=0;
 for(let i=1;i<notes.length;i++){
  const d=Math.sign(notes[i]-notes[i-1]);
  if(d&&direction&&d!==direction)turns++;
  if(d)direction=d;
  if(notes[i]===notes[i-1])repeated++;
 }
 score+=Math.min(4,turns)*.5-Math.max(0,repeated-notes.length*.27)*1.5;
 const span=Math.max(...notes)-Math.min(...notes);
 score-=Math.max(0,span-19)*.35;
 if(rhythm?.length){
  for(let i=0;i<rhythm.length;i++){
   if(rhythm[i]?.phraseEnd&&harmony?.[i])score+=harmony[i].notes.has(notes[i]%12)?2:-2;
  }
 }
 return score;
}
function optimizePhraseCandidates(notes,candidates,rhythm,harmony,key){
 if(musicGoal()!=='song'||notes.length<3)return notes;
 // Bounded coordinate search: consider alternatives in context, never change
 // a remembered motif merely to eliminate a harmless expressive dissonance.
 const chosen=notes.slice();
 for(let pass=0;pass<2;pass++){
  for(let i=1;i<chosen.length-1;i++){
   const original=chosen[i];
   const options=candidates.filter(n=>Math.abs(n-original)<=4&&Math.abs(n-chosen[i-1])<=9&&Math.abs(n-chosen[i+1])<=9);
   let best=original,bestScore=phraseCandidateScore(chosen,rhythm,harmony,key);
   for(const candidate of options){
    chosen[i]=candidate;
    const candidateScore=phraseCandidateScore(chosen,rhythm,harmony,key)-Math.abs(candidate-original)*.5;
    if(candidateScore>bestScore+.4){best=candidate;bestScore=candidateScore;}
   }
   chosen[i]=best;
  }
 }
 return chosen;
}
// Precompose one complete form before playback. The next form is generated
// only after the preceding form finishes, avoiding a single 60-minute identity.
let composedSongQueue=[],composedSongCycle=-1,playbackBar=0;
// All additional instruments are composed before the song starts. A plan is
// immutable during playback; note events are played from this plan, not regenerated.
function arrangementSelections(){
 const leadLayers=['leadLayer1','leadLayer2'].map(id=>[id,arrangementInstrument(id)]).filter(x=>x[1]);
 const backingLayers=['backingLayer1','backingLayer2'].map(id=>[id,arrangementInstrument(id)]).filter(x=>x[1]);
 return {leadLayers,backingLayers,backing:arrangementInstrument('backingInstrument')};
}
function scoreArrangementPlan(m,plan){
 let penalty=0,previous=new Map(),lastBass=null;
 for(let i=0;i<plan.length;i++){
  const lead=m.notes[i],events=plan[i];
  const used=[];
  for(const e of events){
   if(!e.inst||!e.pitches.length)continue;
   for(const n of e.pitches){
    if(n<e.inst.range[0]||n>e.inst.range[1])penalty+=12;
    if(e.id.startsWith('lead')&&Math.abs(n-lead)<3)penalty+=2;
    if(used.some(x=>Math.abs(x-n)<2))penalty+=1.2;
    used.push(n);
   }
   const old=previous.get(e.id);
   if(old!==undefined&&Math.abs(e.pitches[0]-old)>13)penalty+=2;
   previous.set(e.id,e.pitches[0]);
   if(e.id==='backingLayer1'){
    if(lastBass!==null&&Math.abs(e.pitches[0]-lastBass)>14)penalty+=2;
    lastBass=e.pitches[0];
   }
  }
 }
 return penalty;
}
function auditArrangementPlan(m,plan){
 // Repair crowded counterlines and impossible ranges without erasing the groove.
 for(let i=0;i<plan.length;i++){
  const lead=m.notes[i],events=plan[i],occupied=[];
  for(const e of events){
   const cleaned=[];
   for(let n of e.pitches){
    n=arrangementPitch(e.inst,n);
    if(n===null)continue;
    if(e.id.startsWith('lead')&&Math.abs(n-lead)<3){
     const alternative=nearestChordTone(m.harmony?.[i]?.pcs,n+(n<=lead?-5:5),e.inst);
     if(alternative!==null&&Math.abs(alternative-lead)>3)n=alternative;
    }
    if(e.id!=='backingLayer1'&&occupied.some(x=>Math.abs(x-n)<2)){
     const shifted=arrangementPitch(e.inst,n+(n<lead?-12:12));
     if(shifted!==null)n=shifted;
    }
    cleaned.push(n);occupied.push(n);
   }
   e.pitches=[...new Set(cleaned)];
  }
  plan[i]=events.filter(e=>e.pitches.length);
 }
 return plan;
}

// V9: independent symbolic arrangement analysis and bounded local optimization.
function analyzeArrangement(m,plan,beatMs,genre){
 const weights=genre==='ジャズ'?{parallel:.35,dissonance:.65}:genre==='ロック'?{parallel:.2,dissonance:1.1}:{parallel:1,dissonance:1};
 const scores={counterpoint:0,harmony:0,melody:0,rhythm:0,playability:0,balance:0,form:0};
 const issues=[], timeline=[], previous=new Map(), pairs=new Map();
 const add=(kind,cost,i,event=null)=>{scores[kind]+=cost;if(event&&cost>0)issues.push({kind,cost,i,event});};
 let time=0;
 for(let i=0;i<plan.length;i++){
  const r=m.rhythm?.[i],slot=(r?.beats??1)*beatMs;
  timeline.push({id:'main',n:m.notes[i],start:time,end:time+slot*(r?.articulation??.85),i});
  for(const e of plan[i]){
   for(const n of e.pitches){
    if(!Number.isFinite(n)||n<e.inst.range[0]||n>e.inst.range[1])add('playability',20,i,e);
    if(e.delayMs<0||e.holdMs<=0)add('rhythm',10,i,e);
    const old=previous.get(e.id);
    if(old!==undefined&&Math.abs(n-old)>12)add('playability',(Math.abs(n-old)-12)*.3,i,e);
    previous.set(e.id,n);
    const pcs=m.harmony?.[i]?.pcs;
    if(pcs?.length&&!pcs.some(p=>((p-n)%12+12)%12===0)){
     const next=plan[i+1]?.find(x=>x.id===e.id)?.pitches[0];
     if(next===undefined||Math.abs(next-n)>2)add('harmony',1.3*weights.dissonance,i,e);
    }
    timeline.push({id:e.id,n,start:time+e.delayMs,end:time+e.delayMs+e.holdMs,i,e});
   }
   if(e.id.startsWith('lead')&&e.velocity>75)add('balance',(e.velocity-75)*.12,i,e);
  }
  if(i&&Math.abs(m.notes[i]-m.notes[i-1])>12)add('melody',2,i);
  if(r?.phraseEnd&&m.harmony?.[i]?.notes&&!m.harmony[i].notes.has(m.notes[i]%12))add('melody',2,i);
  const energy=songSectionAt(r?.measure??0).energy;
  if(energy<.4&&plan[i].length>4)add('form',(plan[i].length-4)*.6,i);
  time+=slot+(r?.rest??0)*beatMs;
 }
 timeline.sort((a,b)=>a.start-b.start);
 let active=[];
 for(const b of timeline){
  active=active.filter(a=>a.end>b.start);
  for(const a of active){
   if(a.id===b.id)continue;
   const overlap=Math.min(a.end,b.end)-b.start;
   if(overlap<Math.min(45,beatMs*.1))continue;
   const x=a.id<b.id?a:b,y=x===a?b:a;
   const interval=Math.abs(x.n-y.n),pc=interval%12;
   const target=b.e?b:a;
   const factor=Math.min(1,overlap/(beatMs*.45));
   if(interval<3)add('balance',2.8*factor,target.i,target.e);
   if(interval<12&&Math.min(a.n,b.n)<48&&[1,2,3,4].includes(pc))add('balance',2*factor,target.i,target.e);
   if([1,6,11].includes(pc))add('counterpoint',1.1*factor*weights.dissonance,target.i,target.e);
   const key=x.id+'|'+y.id,old=pairs.get(key);
   if(old&&old.i!==b.i){
    const dx=x.n-old.x,dy=y.n-old.y;
    if(dx&&dy&&Math.sign(dx)===Math.sign(dy)&&pc===old.pc&&(pc===0||pc===7))add('counterpoint',2.5*weights.parallel,target.i,target.e);
    if((x.n-y.n)*(old.x-old.y)<0)add('counterpoint',.7,target.i,target.e);
   }
   pairs.set(key,{x:x.n,y:y.n,pc,i:b.i});
  }
  active.push(b);
 }
 return {penalty:Object.values(scores).reduce((a,b)=>a+b,0),scores,issues};
}
function optimizeArrangementV9(m,plan,beatMs,genre){
 const initial=analyzeArrangement(m,plan,beatMs,genre);
 let current=initial;
 // Restrict the search to the worst events and accept only measurable improvements.
 for(let pass=0;pass<2;pass++){
  const targets=[...new Set(current.issues.sort((a,b)=>b.cost-a.cost).map(x=>x.event))].slice(0,10);
  for(const e of targets){
   if(e.pitches.length!==1)continue;
   const original=e.pitches[0],i=plan.findIndex(row=>row.includes(e));
   const pcs=m.harmony?.[i]?.pcs;
   if(!pcs?.length)continue;
   const options=[-12,-7,-5,-4,-3,-2,2,3,4,5,7,12].map(d=>original+d).filter(n=>n>=e.inst.range[0]&&n<=e.inst.range[1]&&pcs.some(p=>((p-n)%12+12)%12===0)).sort((a,b)=>Math.abs(a-original)-Math.abs(b-original)).slice(0,5);
   let best=original,bestCost=current.penalty;
   for(const n of options){
    e.pitches[0]=n;
    const trial=analyzeArrangement(m,plan,beatMs,genre);
    const cost=trial.penalty+Math.abs(n-original)*.08;
    if(cost<bestCost-.05){best=n;bestCost=cost;}
   }
   e.pitches[0]=best;
   current=analyzeArrangement(m,plan,beatMs,genre);
  }
 }
 return {before:initial.penalty,after:current.penalty,components:current.scores};
}

// V10: joint phrase search, explicit non-chord tone labels and measured output monitoring.
let mixAnalyser=null, mixSamples=null, mixGain=null, mixPeak=0;
function monitorMixV10(){
 if(!mixAnalyser)return;
 mixAnalyser.getFloatTimeDomainData(mixSamples);
 let peak=0,sum=0;for(const x of mixSamples){peak=Math.max(peak,Math.abs(x));sum+=x*x;}
 mixPeak=Math.max(peak,mixPeak*.92);
 const rms=Math.sqrt(sum/mixSamples.length);
 if(mixGain){const target=peak>.98?Math.max(.45,mixGain.gain.value*.85):rms<.3?Math.min(1,mixGain.gain.value+.015):mixGain.gain.value;mixGain.gain.setTargetAtTime(target,audioContext.currentTime,.08);}
}
function toneClassV10(m,i){
 const n=m.notes[i],p=m.notes[i-1],q=m.notes[i+1],h=m.harmony?.[i],prev=m.harmony?.[i-1];
 if(!h||h.notes.has(n%12))return 'chord';
 const step=(a,b)=>Number.isFinite(a)&&Number.isFinite(b)&&Math.abs(a-b)>0&&Math.abs(a-b)<=2;
 const resolves=q!==undefined&&h.notes.has(q%12)&&step(n,q);
 if(p===n&&prev?.notes.has(n%12)&&resolves&&q<n)return 'rearticulated-suspension';
 if(step(p,n)&&resolves&&Math.sign(n-p)===Math.sign(q-n))return 'passing';
 if(step(p,n)&&resolves&&p===q)return 'neighbor';
 if(q===n&&m.harmony?.[i+1]?.notes.has(n%12))return 'anticipation';
 return 'unresolved';
}
function motifDistanceV10(a,b){
 const k=Math.min(a.length,b.length);if(k<3)return 0;
 let cost=0;for(let i=1;i<k;i++){cost+=Math.min(6,Math.abs((a[i].n-a[i-1].n)-(b[i].n-b[i-1].n)));cost+=Math.min(2,Math.abs(a[i].beats-b[i].beats));}return cost/(k-1);
}
function jointOptimizeV10(m,beatMs,backing){
 const plan=m.arrangementPlan,base=[];let previous=null;
 for(let i=0;i<m.notes.length;i++){
 const h=m.harmony?.[i],r=m.rhythm?.[i];
 const changed=i===0||h?.harmonicStep!==m.harmony?.[i-1]?.harmonicStep;
 if(m.accompanied&&h&&changed)previous=enhancedVoicing(h,m.notes[i],backing,previous,r?.measure??0);
 base.push(m.accompanied&&h&&previous?[...previous]:[]);
 }
 const genre=personalityAt(m.rhythm?.[0]?.measure??songMeasure).genre;
 const original=m.notes.slice();
 const score=()=>{
 const full=plan.map((row,i)=>[...row,...(base[i].length?[{id:'basic',inst:backing,pitches:base[i],velocity:48,holdMs:(m.rhythm?.[i]?.beats??1)*beatMs,delayMs:0}]:[])]);
 let cost=analyzeArrangement(m,full,beatMs,genre).penalty;
 for(let i=0;i<m.notes.length;i++){if(toneClassV10(m,i)==='unresolved')cost+=m.rhythm?.[i]?.beatPosition===0?4:1.5;cost+=Math.abs(m.notes[i]-original[i])*.22;}
 for(const t of m.themeTargets||[])cost+=t.weight*motifDistanceV10(t.ref,t.indices.map(i=>({n:m.notes[i],beats:m.rhythm[i].beats})));
 return cost;
 };
 const before=score();let best=before;
 const [lo,hi]=getRangeForMelody(m.inst);
 // Search coherent blocks, retaining rhythm and harmony labels.
 for(let start=0;start<m.notes.length;start+=8){
 const end=Math.min(start+8,m.notes.length),saved=m.notes.slice(start,end),savedBase=base.slice(start,end).map(x=>x.slice());
 let winner=saved.slice(),winnerBase=savedBase;
 for(const direction of [-1,1,0]){
 for(let i=start;i<end;i++){
 const h=m.harmony?.[i];let n=saved[i-start];
 if(!rHook21(m,i)&&h&&toneClassV10(m,i)==='unresolved'){
 const opts=[n-2,n-1,n+1,n+2].filter(x=>x>=lo&&x<=hi&&h.notes.has(x%12));
 if(opts.length)n=opts.sort((a,b)=>Math.abs(a-n-direction)-Math.abs(b-n-direction))[0];}
 m.notes[i]=n;
 base[i]=savedBase[i-start].map(x=>{const y=x+direction*12;return direction&&y>=backing.range[0]&&y<=backing.range[1]&&Math.abs(y-n)>Math.abs(x-n)?y:x;}).sort((a,b)=>a-b);
 }
 const value=score();if(value<best){best=value;winner=m.notes.slice(start,end);winnerBase=base.slice(start,end).map(x=>x.slice());}
 m.notes.splice(start,end-start,...saved);for(let i=start;i<end;i++)base[i]=savedBase[i-start].slice();
 }
 m.notes.splice(start,end-start,...winner);for(let i=start;i<end;i++)base[i]=winnerBase[i-start];
 }
 m.basicPlan=base;m.jointScore={before,after:best,classes:m.notes.map((_,i)=>toneClassV10(m,i))};
}
function analyzeSongThemesV10(queue){
 const bars=new Map();for(const m of queue)for(let i=0;i<m.notes.length;i++){const r=m.rhythm?.[i];if(!r)continue;const b=r.measure;if(!bars.has(b))bars.set(b,[]);bars.get(b).push({n:m.notes[i],beats:r.beats});}
 const themes=new Map();for(const [b,notes] of bars){const sec=songSectionAt(b),key=sec.name+':'+sec.offset%4;if(themes.has(key)){const d=motifDistanceV10(themes.get(key),notes);for(const m of queue)if(m.rhythm?.[0]?.measure===b)m.themeDistance=d;}else themes.set(key,notes);}
}

// V11: phrase recurrence influences actual notes prior to arrangement generation.
let recurrenceV11=new Map();
function themeRewriteV11(m){
 const groups=new Map();
 for(let i=0;i<m.notes.length;i++){const r=m.rhythm?.[i];if(!r)continue;const sec=songSectionAt(r.measure);if(!['Aメロ','サビ','Bメロ'].includes(sec.name))continue;const key=sec.name+':'+sec.offset%4; if(!groups.has(key))groups.set(key,[]);groups.get(key).push(i);}
 const [lo,hi]=getRangeForMelody(m.inst),scale=new Set(D.SCALES[m.scaleName].map(x=>(x+m.key)%12));
 for(const [key,indices] of groups){
 const row=indices.map(i=>({n:m.notes[i],beats:m.rhythm[i].beats}));
 const ref=recurrenceV11.get(key);if(!ref){if(row.length>=3)recurrenceV11.set(key,row);continue;}if(row.length<3)continue;
 const original=m.notes.slice(),distance=()=>motifDistanceV10(ref,indices.map(i=>({n:m.notes[i],beats:m.rhythm[i].beats})));
 const weight=key.startsWith('サビ')?1.8:1.1;
 const cost=()=>weight*Math.abs(distance()-.65)+indices.reduce((v,i)=>v+Math.abs(m.notes[i]-original[i])*.12+(toneClassV10(m,i)==='unresolved'?1.4:0)+(i&&Math.abs(m.notes[i]-m.notes[i-1])>9?2:0),0)/indices.length;
 const before=distance();let best=cost(),winner=original.slice();
 for(const strength of [.45,.75,1]){m.notes.splice(0,m.notes.length,...original);for(let j=1;j<indices.length;j++){const i=indices[j],k=Math.min(ref.length-1,Math.round(j*(ref.length-1)/(indices.length-1)));const target=m.notes[indices[0]]+ref[k].n-ref[0].n;const desired=original[i]+strength*(target-original[i]);let opts=[];for(let n=Math.max(lo,original[i]-7);n<=Math.min(hi,original[i]+7);n++)if(scale.has(n%12))opts.push(n);if(opts.length)m.notes[i]=opts.sort((a,b)=>Math.abs(a-desired)-Math.abs(b-desired))[0];}const c=cost();if(c<best){best=c;winner=m.notes.slice();}}
 m.notes.splice(0,m.notes.length,...winner);m.themeRewrite={before,after:distance()};(m.themeTargets??=[]).push({indices:[...indices],ref,weight});
 }
}
// Individual channel taps are analysis-only: never connect them to audible output.
let channelMetersV11=[],mixTrimV11=Array(6).fill(1),mixTickV11=0;
function setupChannelMetersV11(){
 if(typeof synth.connectChannel!=='function')return;
 for(let ch=0;ch<6;ch++){try{const node=audioContext.createAnalyser();node.fftSize=1024;node.smoothingTimeConstant=.75;synth.connectChannel(node,ch);channelMetersV11.push({ch,node,wave:new Float32Array(1024),fft:new Float32Array(512),rms:0,bands:[]});}catch(e){console.warn('Channel analysis unavailable',ch,e);}}
}
function expressionV11(ch,level){return Math.round(Math.max(0,Math.min(127,level*1.27*(musicGoal()==='song'?mixTrimV11[ch]??1:1))));}
function monitorChannelsV11(){
 if(!channelMetersV11.length)return;
 for(const m of channelMetersV11){m.node.getFloatTimeDomainData(m.wave);m.node.getFloatFrequencyData(m.fft);let sum=0,peak=0;for(const x of m.wave){sum+=x*x;peak=Math.max(peak,Math.abs(x));}m.rms=.65*m.rms+.35*Math.sqrt(sum/m.wave.length);m.peak=peak;const edges=[0,160,400,1000,2500,6000,24000];m.bands=Array(6).fill(0);for(let i=0;i<m.fft.length;i++){const f=i*audioContext.sampleRate/1024;const b=edges.findIndex((x,j)=>j>0&&f<x)-1;if(b>=0&&Number.isFinite(m.fft[i]))m.bands[b]+=10**(m.fft[i]/10);} }
 if(++mixTickV11%4)return;
 const lead=channelMetersV11.find(m=>m.ch===0);if(!lead||lead.rms<.008)return;
 for(const m of channelMetersV11){if(m.ch===0||m.rms<.004)continue;const a=lead.bands.reduce((x,y)=>x+y,0),b=m.bands.reduce((x,y)=>x+y,0);const overlap=a&&b?lead.bands.reduce((v,x,i)=>v+Math.min(x/a,m.bands[i]/b),0):0;const target=m.rms>lead.rms*(m.ch===1?.95:.8)&&overlap>.55?Math.max(.65,mixTrimV11[m.ch]-.035):Math.min(1,mixTrimV11[m.ch]+.012);mixTrimV11[m.ch]=target;}
 applyMelodyExpression();
}

function prearrangeMelody(m,selection){
 const tempo=Math.max(40,Math.min(240,Number(el.melodyTempo?.value)||100));
 const beatMs=track14?60000/track14.bpm:60000/(musicGoal()==='song'?Math.max(40,Math.min(240,tempo*personalityAt(m.rhythm?.[0]?.measure??songMeasure).tempo)):tempo);
 const plan=[];
 for(let i=0;i<m.notes.length;i++){
  const events=[];
  const slotMs=(m.rhythm?.[i]?.beats??1)*beatMs;
  arrangeIndependentParts(m,i,beatMs,slotMs,runToken,selection.leadLayers,selection.backingLayers,selection.backing||m.inst,events);
  plan.push(events);
 }
 const before=scoreArrangementPlan(m,plan);
 auditArrangementPlan(m,plan);
 m.arrangementPlan=plan;
 m.arrangementScore=musicGoal()==='song'?optimizeArrangementV9(m,plan,beatMs,personalityAt(m.rhythm?.[0]?.measure??songMeasure).genre):{before,after:scoreArrangementPlan(m,plan)};
 if(musicGoal()==='song')jointOptimizeV10(m,beatMs,selection.backing||m.inst);
 return m;
}

// V12: song-wide themes, independent of training-question boundaries.
function rebuildLongThemesV12(queue){
 const bars=new Map(),themes=new Map();
 for(const m of queue)for(let i=0;i<m.notes.length;i++){
  const r=m.rhythm?.[i];if(!r)continue;
  if(!bars.has(r.measure))bars.set(r.measure,[]);
  bars.get(r.measure).push({m,i,r});
 }
 const snapshot=rows=>rows.map(({m,i,r})=>({n:m.notes[i],beats:r.beats}));
 const sample=(ref,j,count)=>ref[Math.round(j*(ref.length-1)/Math.max(1,count-1))];
 for(const [bar,rows] of bars){
  const sec=songSectionAt(bar);if(sec.offset%4!==0||!['Aメロ','Bメロ','サビ'].includes(sec.name))continue;
  const block=Array.from({length:4},(_,j)=>bars.get(bar+j)||[]);
  if(block.some(x=>!x.length))continue;
  const key=sec.name+':'+Math.floor(sec.offset/4)%2;
  const ref=themes.get(key);
  if(!ref){themes.set(key,block.map(snapshot));continue;}
  const all=block.flat(),reference=ref.flat(),original=snapshot(all);
  const anchor=original[0].n;
  const score=()=>{
   const current=snapshot(all);let cost=0;
   for(let j=0;j<all.length;j++){
    const {m,i,r}=all[j],n=m.notes[i],target=sample(reference,j,all.length).n-reference[0].n;
    cost+=Math.min(12,Math.abs(n-current[0].n-target))*.65;
    if(j){const d=n-current[j-1].n;cost+=Math.max(0,Math.abs(d)-7)*1.5;}
    if(m.harmony?.[i]?.notes&&!m.harmony[i].notes.has(n%12))cost+=r.beatPosition===0?2:0.6;
    cost+=Math.abs(n-original[j].n)*.15;
   }
   return cost;
  };
  let best=score(),winner=original.map(x=>x.n);
  for(const strength of [.45,.75,1]){
   for(let j=0;j<all.length;j++){
    const {m,i}=all[j], [lo,hi]=getRangeForMelody(m.inst),scale=new Set(D.SCALES[m.scaleName].map(x=>(x+m.key)%12));
    const target=anchor+sample(reference,j,all.length).n-reference[0].n;
    const desired=original[j].n+strength*(target-original[j].n);let opts=[];
    for(let n=Math.max(lo,original[j].n-9);n<=Math.min(hi,original[j].n+9);n++)if(scale.has(n%12))opts.push(n);
    m.notes[i]=opts.length?opts.sort((a,b)=>Math.abs(a-desired)-Math.abs(b-desired))[0]:original[j].n;
   }
   const c=score();if(c<best){best=c;winner=snapshot(all).map(x=>x.n);}
  }
  all.forEach(({m,i},j)=>{m.notes[i]=winner[j];});
  // Rhythm variation within each unchanged harmony segment: preserve meter,
  // note count, chord-change positions and phrase boundaries across questions.
  for(let b=0;b<4;b++){
   const row=block[b],source=ref[b];let start=0;
   while(start<row.length){
    let end=start+1;const h=row[start].m.harmony?.[row[start].i]?.harmonicStep;
    while(end<row.length&&row[end].m.harmony?.[row[end].i]?.harmonicStep===h)end++;
    const group=row.slice(start,end),total=group.reduce((v,x)=>v+x.r.beats,0);
    if(group.length>=2&&total>=group.length*.25&&!group.slice(0,-1).some(x=>x.r.rest)){
     const weights=group.map((x,j)=>.55*x.r.beats+.45*sample(source,start+j,row.length).beats);
     // Alternating long-short variation, with a positive minimum duration.
     const varied=weights.map((w,j)=>w*(j%2===0?1.18:.82));
     const sum=varied.reduce((a,b)=>a+b,0);let pos=group[0].r.beatPosition,remaining=total;
     group.forEach(({r},j)=>{const beats=j===group.length-1?remaining:.25+(total-group.length*.25)*varied[j]/sum;r.beatPosition=pos;r.beats=beats;pos+=beats;remaining-=beats;r.articulation=Math.max(.65,Math.min(.99,r.articulation*(j%2===0?1.02:.94)));});
    }
    start=end;
   }
  }
  // Keep the reconstructed contour in the subsequent joint optimizer.
  const groups=new Map();for(const x of all){if(!groups.has(x.m))groups.set(x.m,[]);groups.get(x.m).push(x.i);}
  for(const [m,indices] of groups)(m.themeTargets??=[]).push({indices,ref:indices.map(i=>({n:m.notes[i],beats:m.rhythm[i].beats})),weight:3});
 }
}


// V13: nested phrase references and meter-preserving note-count variation.
function hierarchicalThemesV13(queue){
 const bars=new Map(),refs=new Map();
 for(const m of queue)for(let i=0;i<m.notes.length;i++){const r=m.rhythm[i];if(!bars.has(r.measure))bars.set(r.measure,[]);bars.get(r.measure).push({m,i,r});}
 const snap=rows=>rows.map(x=>({n:x.m.notes[x.i],beats:x.r.beats}));
 for(const size of [16,8,4])for(const [bar] of bars){
  const sec=songSectionAt(bar);if(sec.offset%size||sec.offset+size>sec.bars||!['Aメロ','Bメロ','サビ'].includes(sec.name))continue;
  const block=Array.from({length:size},(_,j)=>bars.get(bar+j)||[]);if(block.some(row=>!row.length))continue;
  const key=size+':'+sec.name+':'+sec.offset%size, ref=refs.get(key);
  if(!ref){refs.set(key,block.map(snap));continue;}
  const rows=block.flat(),original=snap(rows),anchor=original[0].n,refAnchor=ref[0][0].n;
  const targets=block.flatMap((row,b)=>row.map((_,j)=>anchor+ref[b][Math.round(j*(ref[b].length-1)/Math.max(1,row.length-1))].n-refAnchor));
  const score=()=>rows.reduce((sum,x,j)=>{const n=x.m.notes[x.i],prev=j?rows[j-1].m.notes[rows[j-1].i]:n;return sum+Math.abs(n-targets[j])*.7+Math.abs(n-original[j].n)*.25+Math.max(0,Math.abs(n-prev)-7)*1.5+(x.m.harmony?.[x.i]?.notes&&!x.m.harmony[x.i].notes.has(n%12)?(x.r.beatPosition===0?3:.6):0);},0);
  let best=score(),winner=original.map(x=>x.n);
  for(const strength of [.35,.65,.9]){rows.forEach((x,j)=>{const [lo,hi]=getRangeForMelody(x.m.inst),pcs=new Set(D.SCALES[x.m.scaleName].map(v=>(v+x.m.key)%12));const target=original[j].n+strength*(targets[j]-original[j].n);let n=original[j].n,cost=Infinity;for(let k=Math.max(lo,n-9),end=Math.min(hi,n+9);k<=end;k++)if(pcs.has(k%12)&&Math.abs(k-target)<cost){cost=Math.abs(k-target);n=k;}x.m.notes[x.i]=n;});const c=score();if(c<best){best=c;winner=rows.map(x=>x.m.notes[x.i]);}}
  rows.forEach((x,j)=>{x.m.notes[x.i]=winner[j];});
 }
}
function varyNoteCountsV13(queue){
 for(const m of queue){
  const rows=m.notes.map((n,i)=>({n,r:{...m.rhythm[i]},h:m.harmony?.[i],c:m.chordInfos?.[i],p:m.phrasePlan?.[i]}));
  const out=[];let edits=0;const limit=Math.max(1,Math.floor(rows.length/4));
  for(let i=0;i<rows.length;i++){
   const a=rows[i],b=rows[i+1],sec=songSectionAt(a.r.measure),eligible=['Aメロ','Bメロ','サビ'].includes(sec.name)&&sec.offset>=4;
   const contiguous=b&&a.r.measure===b.r.measure&&Math.abs(a.r.beatPosition+a.r.beats-b.r.beatPosition)<1e-6&&!a.r.rest&&!a.r.phraseEnd&&a.h?.harmonicStep===b.h?.harmonicStep;
   if(eligible&&edits<limit&&rows.length-edits>3&&contiguous&&Math.abs(a.n-b.n)<=4&&a.r.beats+b.r.beats<=2&&Math.random()<.23){out.push({...a,r:{...a.r,beats:a.r.beats+b.r.beats,rest:b.r.rest,phraseEnd:b.r.phraseEnd,articulation:b.r.articulation}});i++;edits++;continue;}
   if(eligible&&edits<limit&&rows.length+edits<32&&a.r.beats>=.75&&!a.r.phraseEnd&&Math.random()<.28){const first=a.r.beats>=1.5?a.r.beats*2/3:a.r.beats/2,second=a.r.beats-first;const [lo,hi]=getRangeForMelody(m.inst),pcs=new Set(D.SCALES[m.scaleName].map(v=>(v+m.key)%12));const candidates=[a.n-2,a.n-1,a.n+1,a.n+2].filter(n=>n>=lo&&n<=hi&&pcs.has(n%12));const n=candidates.length?candidates[Math.floor(Math.random()*candidates.length)]:a.n;out.push({...a,r:{...a.r,beats:first,rest:0,phraseEnd:false}},{...a,n,r:{...a.r,beats:second,beatPosition:a.r.beatPosition+first}});edits++;continue;}
   out.push(a);
  }
  m.notes=out.map(x=>x.n);m.rhythm=out.map(x=>x.r);if(m.harmony)m.harmony=out.map(x=>x.h);if(m.chordInfos)m.chordInfos=out.map(x=>x.c);if(m.phrasePlan)m.phrasePlan=out.map(x=>x.p);
  m.themeTargets=[{indices:m.notes.map((_,i)=>i),ref:out.map(x=>({n:x.n,beats:x.r.beats})),weight:3}];
 }
}


// V15: select a singable hook and develop it over complete musical phrases.
function lyricalThemesV15(queue){
 const bars=new Map(), hooks=new Map(), ranges=new Map();
 for(const m of queue){ranges.set(m,getRangeForMelody(m.inst));for(let i=0;i<m.notes.length;i++){const r=m.rhythm[i];if(!bars.has(r.measure))bars.set(r.measure,[]);bars.get(r.measure).push({m,i,r});}}
 const shapes=[[0,2,4,2,5,4,2,0],[0,0,3,2,5,7,4,2],[0,-2,0,3,2,5,4,0],[0,4,3,2,0,2,5,4],[0,2,0,-2,0,4,3,2]];
 const note=x=>x.m.notes[x.i];
 const options=x=>{const [lo,hi]=ranges.get(x.m),pcs=new Set(D.SCALES[x.m.scaleName].map(v=>(v+x.m.key)%12));return Array.from({length:hi-lo+1},(_,j)=>lo+j).filter(n=>pcs.has(n%12));};
 let previous=null;
 for(const [bar] of bars){const sec=songSectionAt(bar);if(sec.offset%4)continue;
 const rows=[];for(let b=0;b<Math.min(4,sec.bars-sec.offset);b++)rows.push(...(bars.get(bar+b)||[]));if(rows.length<3)continue;
 const original=rows.map(note), pool=rows.map(options), family=sec.name, phase=Math.floor(sec.offset/4)%4;
 const ref=hooks.get(family), chorus=family==='サビ', quiet=family==='イントロ'||family==='アウトロ';
 const center=original.reduce((a,b)=>a+b,0)/original.length;
 const anchor=Math.round(center+(chorus?3:quiet?-2:0));
 const score=ns=>{let cost=0,peak=0,repeat=0;for(let j=0;j<ns.length;j++){const x=rows[j],n=ns[j],h=x.m.harmony?.[x.i],p=j?ns[j-1]:previous,d=p==null?0:n-p;peak=Math.max(peak,n);if(d===0)repeat++;cost+=Math.max(0,Math.abs(d)-5)*.8+Math.max(0,Math.abs(d)-9)*2;if(j>1&&Math.abs(ns[j-1]-ns[j-2])>=5&&Math.sign(d)===Math.sign(ns[j-1]-ns[j-2]))cost+=1.5;if(h&&!h.notes.has(n%12)){const q=ns[j+1];const resolved=q!==undefined&&Math.abs(q-n)<=2&&h.notes.has(q%12);cost+=resolved?.15:(x.r.beatPosition===0||x.r.beats>=1?2.5:.8);}if(x.r.phraseEnd&&h&&!h.notes.has(n%12))cost+=3;}
 const span=Math.max(...ns)-Math.min(...ns);cost+=Math.max(0,5-span)*1.5+Math.max(0,span-14)*1.2+Math.max(0,repeat-ns.length*.4)*1.2;
 if(ref){for(let j=1;j<ns.length;j++){const k=Math.round(j*(ref.length-1)/(ns.length-1));cost+=Math.min(8,Math.abs((ns[j]-ns[0])-(ref[k]-ref[0])))*.45;}}
 return cost/ns.length;};
 let best=original,bestCost=score(original)+.45;
 const templates=ref?[ref.map(n=>n-ref[0]),...shapes.slice(0,2)]:shapes;
 for(const shape of templates)for(const shift of [-3,0,3]){const ns=[];for(let j=0;j<rows.length;j++){const x=rows[j],h=x.m.harmony?.[x.i],u=j/(rows.length-1),k=Math.round(u*(shape.length-1)),arc=phase===2?3*Math.sin(Math.PI*u):phase===3?-2*u:0;const target=anchor+shift+shape[k]+arc;const p=ns.at(-1)??previous;let winner=original[j],v=Infinity;for(const n of pool[j]){let c=Math.abs(n-target)*.8+(p==null?0:Math.max(0,Math.abs(n-p)-4)*1.2);if(h&&!h.notes.has(n%12))c+=x.r.phraseEnd?5:x.r.beatPosition===0?2:.4;if(c<v){v=c;winner=n;}}ns.push(winner);}const c=score(ns);if(c<bestCost){bestCost=c;best=ns;}}
 if(!ref&&!quiet)hooks.set(family,best.slice());
 rows.forEach((x,j)=>{x.m.notes[x.i]=best[j];const u=j/(rows.length-1),climax=Math.sin(Math.PI*u);x.r.lyricalVelocity=Math.round((chorus?8:quiet?-5:0)+9*climax-5+(best[j]>(best[j-1]??best[j])+4?4:0));x.r.articulation=Math.max(.65,Math.min(.99,(x.r.articulation??.85)*(.94+.10*climax+(x.r.phraseEnd?.06:0))));});previous=best.at(-1);
 }
 for(const m of queue)m.themeTargets=[{indices:m.notes.map((_,i)=>i),ref:m.notes.map((n,i)=>({n,beats:m.rhythm[i].beats})),weight:5}];
}

// V16: section-specific melodic grammar, shared song DNA and harmonic destinations.
function sectionThemesV16(queue){
 const bars=new Map(), cache=new Map();
 for(const m of queue)for(let i=0;i<m.notes.length;i++){const r=m.rhythm[i];if(!bars.has(r.measure))bars.set(r.measure,[]);bars.get(r.measure).push({m,i,r});}
 const dna=pick([[0,2,1],[0,3,2],[0,-2,1],[0,1,3]]);
 const shapes={'イントロ':[0,2,1,0,0,2,1,0],'Aメロ':[0,0,1,0,-1,0,2,0],'Bメロ':[-2,-1,0,1,2,3,4,5],'サビ':[0,4,3,2,4,5,3,0],'間奏':[0,2,4,2,1,-1,1,0],'アウトロ':[3,2,1,0,1,0,-1,0]};
 let previous=null;
 for(const [bar] of bars){const sec=songSectionAt(bar);if(sec.offset%4)continue;
 const rows=[];for(let b=0;b<Math.min(4,sec.bars-sec.offset);b++)rows.push(...(bars.get(bar+b)||[]));if(!rows.length)continue;
 const family=sec.name,phase=Math.floor(sec.offset/4),key=family+':'+phase%4;
 let shape=cache.get(key);if(!shape){shape=(shapes[family]||shapes['Aメロ']).slice();if(family==='イントロ'||family==='アウトロ'){shape[0]=dna[0];shape[1]=dna[1];shape[2]=dna[2];}else{shape[1]+=dna[1]>0?1:-1;shape[2]+=dna[2]>1?1:0;}if(phase%2&&family==='Aメロ')shape[6]+=1;if(phase%2&&family==='サビ')shape[5]+=1;cache.set(key,shape);}
 const original=rows.map(x=>x.m.notes[x.i]);const center=original.reduce((a,b)=>a+b,0)/original.length;
 const candidates=rows.map(x=>{const [lo,hi]=getRangeForMelody(x.m.inst),pcs=new Set(D.SCALES[x.m.scaleName].map(v=>(v+x.m.key)%12));return Array.from({length:hi-lo+1},(_,j)=>lo+j).filter(n=>pcs.has(n%12));});
 // Beam search preserves section contour even when local chord-tone choices compete.
 let beam=[{cost:0,notes:[],last:previous}];
 for(let j=0;j<rows.length;j++){const x=rows[j],u=j/Math.max(1,rows.length-1),k=Math.min(7,Math.floor(u*8)),h=x.m.harmony?.[x.i];const tension=emotionV17(x.r.measure);const target=center+(shape[k]-2)*(1.25+tension*.9);const next=[];
 for(const state of beam){for(const n of candidates[j]){const d=state.last==null?0:n-state.last;let c=Math.abs(n-target)*.85+Math.max(0,Math.abs(d)-5)*1.4+Math.max(0,Math.abs(d)-9)*3;
 if(h&&!h.notes.has(n%12))c+=(x.r.phraseEnd?5:x.r.beatPosition===0?2.5:.6)*(1.25-.65*tension);
 if(j&&h&&h.notes.has(n%12)&&!h.notes.has(state.last%12)&&Math.abs(d)<=2)c-=.6;
 if(x.r.phraseEnd&&tension<.4)c+=((n-x.m.key+12)%12===0?0:1.4);
 if(j&&k!==Math.floor((j-1)/Math.max(1,rows.length-1)*8)){const want=Math.sign(shape[k]-shape[Math.min(7,Math.floor((j-1)/Math.max(1,rows.length-1)*8))]);if(want&&Math.sign(d)!==want)c+=2.5;}
 if(family==='Aメロ'&&Math.abs(d)>4)c+=1;if(family==='Bメロ'&&d<0&&u>.55)c+=1.4;
 if(j===rows.length-1){const pc=(n-x.m.key+12)%12;if(family==='Bメロ'&&sec.offset+4>=sec.bars)c+=pc===7||pc===11||pc===2?0:3;else if(family==='サビ'||family==='アウトロ')c+=pc===0||pc===4||pc===3?0:2;}
 next.push({cost:state.cost+c,notes:[...state.notes,n],last:n});}}
 if(!next.length)break;next.sort((a,b)=>a.cost-b.cost);beam=next.slice(0,8);}
 const best=beam[0]?.notes;if(best?.length===rows.length){rows.forEach((x,j)=>x.m.notes[x.i]=best[j]);previous=best.at(-1);}else previous=original.at(-1);
 }
 for(const m of queue)m.themeTargets=[{indices:m.notes.map((_,i)=>i),ref:m.notes.map((n,i)=>({n,beats:m.rhythm[i].beats})),weight:8}];
}

// V19: phrase-level accompaniment independent of question and harmony attacks.
const backingActive19=new Set();let backingPreset19=null;
function resetBacking19(){for(const n of backingActive19)try{synth?.noteOff(1,n);}catch(_){}backingActive19.clear();backingPreset19=null;}
function planBacking19(queue,selection,bpm){
 const rows=[];let time=0;const beatMs=60000/bpm;
 for(const m of queue){m.backing19=[];m.backingInst19=selection.backing||m.inst;for(let i=0;i<m.notes.length;i++){const r=m.rhythm[i],h=m.harmony?.[i],len=r.beats;const inst=m.backingInst19;const key=m.accompanied&&h?`${inst.id}:${h.root}:${[...h.pcs].sort((a,b)=>a-b).join(',')}:${h.inversion??0}`:'none';rows.push({m,i,r,h,len,time,key,inst});time+=len;}}
 const styles=['longArp','hold','bassSplit','common','sync','sparse','wave'];const memory=new Map();let prev=[],prevInst=null,lastExtra={};
 for(let a=0;a<rows.length;){let b=a+1;while(b<rows.length&&rows[b].key===rows[a].key)b++;const first=rows[a],total=rows[b-1].time+rows[b-1].len-first.time;const sec=songSectionAt(first.r.measure);const sk=sec.name+':'+Math.floor(sec.offset/8)%2;if(!memory.has(sk))memory.set(sk,styles[Math.floor(Math.random()*styles.length)]);let style=memory.get(sk);if(bpm>=140&&total<=4)style='common';if(total>=7&&style==='sync')style='longArp';
 let tones=first.key==='none'?[]:(first.m.basicPlan?.[first.i]||[]).filter(n=>first.h.pcs.includes(n%12)&&n>=first.inst.range[0]&&n<=first.inst.range[1]);tones=[...new Set(tones)].sort((x,y)=>x-y);if(tones.length>4)tones=tones.slice(0,4);if(bpm>=140&&tones.length>3)tones=tones.slice(0,3);
 // Retain exact common pitches when possible; avoid low-register clusters.
 if(prevInst===first.inst.id)for(const n of prev){if(first.h?.pcs.includes(n%12)&&!tones.includes(n)){const j=tones.findIndex(x=>x%12===n%12);if(j>=0)tones[j]=n;}}
 tones=[...new Set(tones)].sort((x,y)=>x-y).filter((n,j,arr)=>!j||n>=52||n-arr[j-1]>=5);
 const events=[];const add=(at,ns)=>{if(ns.length)events.push({at,ns});};let held=prevInst===first.inst.id?prev.filter(n=>tones.includes(n)):[];
 if(style==='hold'||style==='common')add(0,tones.filter(n=>!held.includes(n)));
 else if(style==='longArp'||style==='wave'){const seq=style==='wave'?[...tones,...tones.slice(1,-1).reverse()]:tones;const count=Math.min(seq.length,Math.max(1,Math.floor(total*beatMs/360)));for(let j=0;j<count;j++)add(j*total/count,[seq[j]]);}
 else if(style==='bassSplit'){add(0,tones.slice(0,1));add(total*.45,tones.slice(1));}
 else if(style==='sync'){add(Math.min(.5,total*.2),tones.slice(0,2));add(total*.65,tones.slice(2));}
 else {add(0,tones.slice(0,1));add(total*.6,tones.slice(-1));}
 if(first.m.end14&&first.i===first.m.notes.length-1)add(0,tones);
 for(let j=a;j<b;j++){const x=rows[j],offset=x.time-first.time;const attacks=events.filter(e=>e.at>=offset-1e-7&&e.at<offset+x.len-1e-7).map(e=>({delay:Math.max(0,Math.min((e.at-offset)*beatMs,x.len*beatMs-25)),notes:e.ns,velocity:Math.round((bpm>=140?43:50)-(x.len<=.5?5:0))}));x.m.backing19[x.i]={allowed:tones,attacks,style};
 // Limit extra accompaniment attacks in real time, across question boundaries.
 const old=x.m.arrangementPlan[x.i]||[];x.m.arrangementPlan[x.i]=old.filter(e=>{if(!e.id.startsWith('backing'))return true;const at=x.time*beatMs+e.delayMs,min=bpm>=140?850:500;if(at-(lastExtra[e.id]??-Infinity)<min||x.len<=.25)return false;lastExtra[e.id]=at;e.velocity=Math.min(e.velocity,bpm>=140?43:52);if(bpm>=140)e.pitches=e.pitches.slice(0,1);return true;});}
 prev=[...new Set([...held,...events.flatMap(e=>e.ns)])];prevInst=first.inst.id;a=b;
 }
}
function playBacking19(m,i,token){const p=m.backing19[i],inst=m.backingInst19;if(!p)return;if(backingPreset19!==inst.id){resetBacking19();setAccompanimentPreset(inst);backingPreset19=inst.id;}
 for(const n of [...backingActive19])if(!p.allowed.includes(n)){synth.noteOff(1,n);backingActive19.delete(n);}
 for(const e of p.attacks){const fire=()=>{for(const n of e.notes)if(!backingActive19.has(n)){synth.noteOn(1,n,e.velocity);backingActive19.add(n);}};if(e.delay<1)fire();else arrangementEvent(e.delay,token,fire);}
}

// V20: evaluate the final sounding accompaniment, including held common tones.
function optimizeFinalBacking20(queue,bpm,genre){
 const beat=60000/bpm,rows=[],voices=[];let t=0,held=new Map();
 const close=(n,end)=>{const v=held.get(n);if(v){v.end=end;held.delete(n);}};
 for(const m of queue){let qt=t;const end=t+m.rhythm.reduce((s,r)=>s+(r.beats+(r.rest||0))*beat,0);
 for(let i=0;i<m.notes.length;i++){const r=m.rhythm[i],p=m.backing19[i],slot=r.beats*beat;const row={m,i,t,slot,p};rows.push(row);
 for(const n of held.keys())if(!p.allowed.includes(n))close(n,t);
 for(const a of p.attacks)for(const n of a.notes)if(!held.has(n)){const v={id:'basic',n,start:t+a.delay,end,attack:a,row};held.set(n,v);voices.push(v);}
 voices.push({id:'main',n:m.notes[i],start:t,end:t+Math.max(35,slot*r.articulation*(songEnding(r.measure)?.88:1)),row});
 for(const e of m.arrangementPlan[i]){e.holdMs=Math.min(e.holdMs,Math.max(1,end-t-e.delayMs));for(const n of e.pitches)voices.push({id:e.id,n,start:t+e.delayMs,end:t+e.delayMs+e.holdMs,e,row});}
 t+=slot+(r.rest||0)*beat;
 } }
 for(const n of held.keys())close(n,t);
 // Local density in a real-time window, including notes on either side of a question.
 const mains=voices.filter(v=>v.id==='main');let l=0,h=0;
 for(const row of rows){while(l<mains.length&&mains[l].start<row.t-650)l++;while(h<mains.length&&mains[h].start<row.t+650)h++;row.density=(h-l)/1.3;}
 const dis=genre==='ジャズ'?.65:1,par=genre==='ロック'?.25:genre==='ジャズ'?.4:1;
 const pair=(a,b,n=a.n)=>{if(a.id===b.id)return 0;const overlap=Math.min(a.end,b.end)-Math.max(a.start,b.start);if(overlap<35)return 0;const d=Math.abs(n-b.n),pc=d%12,f=Math.min(1,overlap/Math.max(100,beat*.65));return f*((d<3?3:0)+(Math.min(n,b.n)<48&&d<12?2:0)+([1,6,11].includes(pc)?1.4*dis:0));};
 voices.sort((a,b)=>a.start-b.start);const active=[];for(const v of voices){v.neighbors=[];for(let j=active.length-1;j>=0;j--)if(active[j].end<=v.start)active.splice(j,1);for(const a of active){a.neighbors.push(v);v.neighbors.push(a);}active.push(v);}
 const cost=(v,n=v.n)=>v.neighbors.reduce((s,b)=>s+(b.removed?0:pair(v,b,n)),0);
 const prev=new Map();let removed=0,changed=0;
 for(const v of voices){if(v.id==='main'||v.removed)continue;const dense=v.row.density>4.5,very=v.row.density>6;const old=prev.get(v.id);const parallel=n=>{if(!old)return 0;const a=old.row.m.notes[old.row.i],b=v.row.m.notes[v.row.i],d=n-old.n;return d&&b!==a&&Math.sign(d)===Math.sign(b-a)&&Math.abs(n-b)%12===Math.abs(old.n-a)%12&&[0,7].includes(Math.abs(n-b)%12)?2.5*par:0;};
 if(v.e&&v.id.startsWith('backing')){const e=v.e,pcs=v.row.m.harmony?.[v.row.i]?.pcs||[];const base=cost(v)+parallel(v.n);let best=v.n,score=base;for(const d of [-12,-7,-5,-3,3,5,7,12]){const n=v.n+d;if(n<e.inst.range[0]||n>e.inst.range[1]||!pcs.includes(n%12)||e.pitches.includes(n))continue;const c=cost(v,n)+parallel(n)+Math.abs(d)*.045;if(c<score){score=c;best=n;}}if(best!==v.n){e.pitches[e.pitches.indexOf(v.n)]=best;v.n=best;changed++;}if(score>(very?1.1:dense?2.0:4.5)||(very&&old&&v.start-old.start<1100)){e.pitches=e.pitches.filter(n=>n!==v.n);v.removed=true;removed++;continue;}e.velocity=Math.min(e.velocity,very?38:dense?45:55);}
 if(v.id==='basic'){const a=v.attack;const c=cost(v)+parallel(v.n);const other=a.notes.length>1||v.neighbors.some(x=>x.id==='basic'&&!x.removed);if(!v.row.m.end14&&other&&c>(very?3:dense?5:9)){a.notes=a.notes.filter(n=>n!==v.n);v.removed=true;removed++;continue;}a.velocity=Math.min(a.velocity,very?39:dense?45:55);}
 prev.set(v.id,v);
 }
 for(const row of rows){row.p.attacks=row.p.attacks.filter(a=>a.notes.length);row.m.arrangementPlan[row.i]=row.m.arrangementPlan[row.i].filter(e=>e.pitches.length&&e.holdMs>0);}
 return {removed,changed};
}

// V21: recurring two-bar rhythmic/pitch signatures, independent of question boundaries.
function rHook21(m,i){return !!m.rhythm?.[i]?.hook21;}
function hooks21(queue){
 const bars=new Map(), memory=new Map();
 for(const m of queue)for(let i=0;i<m.notes.length;i++){const r=m.rhythm[i];if(!bars.has(r.measure))bars.set(r.measure,[]);bars.get(r.measure).push({m,i,r});}
 const patterns=[[0,0,2,1,4,3,2,0],[0,3,2,0,0,3,4,2],[0,1,3,1,0,-1,1,0],[0,-2,0,2,0,3,2,1],[0,4,2,3,1,2,0,0]];
 for(const [bar,row] of bars){const sec=songSectionAt(bar);if(sec.offset%2||!['Aメロ','Bメロ','サビ'].includes(sec.name))continue;
 const rows=[...row,...(sec.offset+1<sec.bars?bars.get(bar+1)||[]:[])];if(rows.length<3)continue;
 let ref=memory.get(sec.name);if(!ref){const shape=patterns[Math.floor(Math.random()*patterns.length)];ref={shape,anchor:rows[0].m.notes[rows[0].i]};memory.set(sec.name,ref);}
 const phase=Math.floor(sec.offset/2)%4;let last=null;
 for(const x of rows){const {m,i,r}=x,[lo,hi]=getRangeForMelody(m.inst),scale=D.SCALES[m.scaleName],pool=[];for(let n=lo;n<=hi;n++)if(scale.includes((n-m.key+120)%12))pool.push(n);if(!pool.length)continue;
 const anchor=pool.reduce((a,b)=>Math.abs(a-ref.anchor)<=Math.abs(b-ref.anchor)?a:b),ai=pool.indexOf(anchor),meter=METER_BEATS[r.meter]||4;
 const u=((r.measure-bar)+r.beatPosition/meter)/2,k=Math.min(7,Math.floor(u*8));let step=ref.shape[k];if(phase===2&&k>=4)step+=1;if(phase===3&&k>=6)step=0;
 const target=pool[Math.max(0,Math.min(pool.length-1,ai+step))];let best=target,cost=Infinity;
 for(const n of pool){const h=m.harmony?.[i],strong=r.beatPosition===0||r.beats>=1;const c=Math.abs(n-target)*2.5+(last===null?0:Math.max(0,Math.abs(n-last)-7)*2)+(h&&!h.notes.has(n%12)?strong?2:.4:0);if(c<cost){cost=c;best=n;}}
 m.notes[i]=best;last=best;r.hook21=true;
 }
 }
 for(const m of queue)m.themeTargets=[{indices:m.notes.map((_,i)=>i),ref:m.notes.map((n,i)=>({n,beats:m.rhythm[i].beats})),weight:18}];
}
// V21: use a root/defining tone shell in busy passages; no repeated arpeggio attacks.
function sparseBacking21(queue,bpm){
 const rows=[];let t=0;const beat=60000/bpm;
 for(const m of queue)for(let i=0;i<m.notes.length;i++){const r=m.rhythm[i];rows.push({m,i,r,t,p:m.backing19[i],h:m.harmony?.[i]});t+=(r.beats+(r.rest||0))*beat;}
 let l=0,h=0;for(const x of rows){while(l<rows.length&&rows[l].t<x.t-700)l++;while(h<rows.length&&rows[h].t<x.t+700)h++;x.busy=(h-l)/1.4>=4||x.r.beats*beat<=180;}
 let held=[],lastInst=null;for(let a=0;a<rows.length;){let b=a+1;const x=rows[a],key=y=>`${y.m.backingInst19.id}:${y.h?.root}:${y.h?.pcs?.join(',')}:${y.m.accompanied}`;while(b<rows.length&&key(rows[b])===key(x))b++;
 const group=rows.slice(a,b),busy=group.some(y=>y.busy);if(lastInst!==x.m.backingInst19.id)held=[];lastInst=x.m.backingInst19.id;
 if(busy&&x.m.accompanied&&x.h){const inst=x.m.backingInst19,pcs=x.h.pcs,root=x.h.root,def=pcs.find(n=>[3,4].includes((n-root+12)%12))??pcs.find(n=>[5,6,8,10,11].includes((n-root+12)%12))??pcs.find(n=>n!==root);const tones=[];
 for(const pc of [root,def]){if(pc===undefined)continue;const pool=[];for(let n=inst.range[0];n<=inst.range[1];n++)if(n%12===pc)pool.push(n);if(!pool.length)continue;const keep=held.find(n=>n%12===pc);const target=pc===root?43:55;tones.push(keep??pool.reduce((a,b)=>Math.abs(a-target)<=Math.abs(b-target)?a:b));}
 const attacks=tones.filter(n=>!held.includes(n));for(const y of group){y.p.allowed=tones.slice();y.p.attacks=[];y.p.style='shell21';y.m.arrangementPlan[y.i]=y.m.arrangementPlan[y.i].filter(e=>!e.id.startsWith('backing'));}if(attacks.length)x.p.attacks=[{delay:0,notes:attacks,velocity:38}];held=tones;
 }else{for(const y of group){held=held.filter(n=>y.p.allowed.includes(n));for(const e of y.p.attacks)held.push(...e.notes);held=[...new Set(held)];}}
 a=b;
 }
}

async function precomposeSong(token){
 if(musicGoal()!=='song'||el.melodyRhythm?.value!=='musical')return;
 const startingBar=songRhythmCarry?.bar??songMeasure;
 track14=design14(startingBar);const cycle=track14.id;personalityAt(startingBar);previousMusicalKey=null;previousMusicalScale=null;songSoundIdentity.clear();songInstrumentation.clear();
 if(composedSongQueue.length&&composedSongCycle===cycle)return;
 composedSongQueue=[];composedSongCycle=cycle;recurrenceV11.clear();
 const selection=arrangementSelections();
 const endBar=track14.end;
 // A small number of notes per question can require hundreds of questions.
 // Guard against infinite generation if the rhythm configuration changes.
 for(let i=0;i<900;i++){
  const bar=songRhythmCarry?.bar??songMeasure;
  if(bar>=endBar)break;
  const m=generateMelody();
  composedSongQueue.push(m);
  previousMelodyEnding=m.notes.at(-1);
  if(i%6===5){await new Promise(resolve=>setTimeout(resolve,0));if(token!==runToken)return;}
  const after=songRhythmCarry?.bar??songMeasure;
  if(after<=bar&&i>850)break;
 }
 const rhythm17=composedSongQueue.map(m=>m.rhythm.map(r=>({...r})));
 rebuildLongThemesV12(composedSongQueue);
 composedSongQueue.forEach((m,i)=>{m.rhythm=rhythm17[i];});
 hierarchicalThemesV13(composedSongQueue);
 varyNoteCountsV13(composedSongQueue);
 lyricalThemesV15(composedSongQueue);
 sectionThemesV16(composedSongQueue);
 hooks21(composedSongQueue);
 jointCompose18(composedSongQueue);
 const last=composedSongQueue.at(-1);if(last){const i=last.notes.length-1,[lo,hi]=getRangeForMelody(last.inst);const ns=[];for(let n=lo;n<=hi;n++)if(n%12===last.key)ns.push(n);if(ns.length)last.notes[i]=ns.reduce((a,b)=>Math.abs(a-last.notes[i])<=Math.abs(b-last.notes[i])?a:b);last.rhythm[i].articulation=.99;last.end14=true;}

 for(let i=0;i<composedSongQueue.length;i++){
  if(token!==runToken)return;
  prearrangeMelody(composedSongQueue[i],selection);
  if(i%6===5)await new Promise(resolve=>setTimeout(resolve,0));
 }
 if(last?.end14){const i=last.notes.length-1,[lo,hi]=getRangeForMelody(last.inst);const ns=[];for(let n=lo;n<=hi;n++)if(n%12===last.key)ns.push(n);if(ns.length)last.notes[i]=ns.reduce((a,b)=>Math.abs(a-last.notes[i])<=Math.abs(b-last.notes[i])?a:b);if(last.harmony){const pcs=[...new Set([0,2,4].map(j=>(last.key+D.SCALES[last.scaleName][j%D.SCALES[last.scaleName].length])%12))];const chord={root:last.key,degree:0,quality:pcs.includes((last.key+3)%12)?'m':'',pcs,notes:new Set(pcs),inversion:0,measure:last.rhythm[i].measure,slot:0,harmonicStep:-14,groupId:-14,progressionName:'終止',progressionPosition:1,progressionLength:1};last.harmony[i]=chord;last.chordInfos[i]=chordInfo(chord,last.key,last.scaleName,chord.measure);if(last.basicPlan)last.basicPlan[i]=chooseSmoothVoicing(chord,last.notes[i],selection.backing||last.inst,null);last.arrangementPlan[i]=[];}}
 planBacking19(composedSongQueue,selection,track14.bpm);
 sparseBacking21(composedSongQueue,track14.bpm);
 optimizeFinalBacking20(composedSongQueue,track14.bpm,personalityAt(startingBar).genre);
 analyzeSongThemesV10(composedSongQueue);
}
async function nextComposedMelody(token){
 if(musicGoal()!=='song'||el.melodyRhythm?.value!=='musical')return generateMelody();
 if(!composedSongQueue.length)await precomposeSong(token);
 return composedSongQueue.shift()||generateMelody();
}
function generateMelody(){
  personalityAt(songRhythmCarry?.bar??songMeasure);
  let inst=arrangementInstrument('leadInstrument')||chooseInstrument();
  const accompanied=el.melodyComposition?.value==='accompanied';
  const [fullLow,fullHigh]=getRangeForMelody(inst);
  const setting=Number(el.melodyCount.value);
  let count=setting===-1?3+Math.floor(Math.random()*30):setting===0?3+Math.floor(Math.random()*6):setting;
  const continuity=el.melodyContinuity?.value==='on'&&previousMelodyEnding!==null;
  const center=(fullLow+fullHigh)/2;
  // Keep the working register near the previous ending, even if the selected instrument changes.
  const anchor=continuity?Math.max(fullLow,Math.min(fullHigh,previousMelodyEnding)):center;
  let low=fullLow,high=fullHigh;
  if(continuity&&fullHigh-fullLow>18){
    low=Math.max(fullLow,Math.round(anchor)-9);
    high=Math.min(fullHigh,Math.round(anchor)+9);
    if(high-low<8){low=Math.max(fullLow,Math.min(low,fullHigh-12));high=Math.min(fullHigh,low+12);}
  }
  const all=Object.values(D.SCALE_CATEGORIES).flat(),categoryScales=D.SCALE_CATEGORIES[Object.keys(D.SCALE_CATEGORIES)[Number(el.melodyCategory.value)]];
  let scaleName=el.melodyScaleMode.value==='3'?chooseMusicalScale(all):el.melodyScaleMode.value==='1'?pick(all):el.melodyScaleMode.value==='2'?pick(categoryScales):categoryScales[Number(el.melodyScale.value)];
  const allowedKeys=el.melodyKeyMode.value==='1'?Array.from({length:12},(_,i)=>i):[Number(el.melodyKey.value)];
  let key=el.melodyKeyMode.value==='2'?chooseMusicalKey(scaleName):continuity&&allowedKeys.length>1?weightedChoice(allowedKeys,k=>{
    const scale=D.SCALES[scaleName].map(x=>(k+x)%12);
    const distance=Math.min(...scale.map(pc=>Math.min((pc-previousMelodyEnding%12+12)%12,(previousMelodyEnding%12-pc+12)%12)));
    return distance===0?6:distance===1?2:0.3;
  }):pick(allowedKeys);
  if(track14){if(track14.key===null){track14.key=key;track14.scale=scaleName;}else{key=track14.key;scaleName=track14.scale;}}previousMusicalKey=key;previousMusicalScale=scaleName;
  const scaleSet=new Set(D.SCALES[scaleName].map(x=>(key+x)%12));
  const natural=el.melodyStyle?.value==='natural';
  const scaleOnly=el.melodySelection.value==='1'||natural||['harmonic','accompanied'].includes(el.melodyComposition?.value);
  let candidates=Array.from({length:high-low+1},(_,i)=>low+i).filter(n=>!scaleOnly||scaleSet.has(n%12));
  if(!candidates.length){candidates=Array.from({length:fullHigh-fullLow+1},(_,i)=>fullLow+i).filter(n=>!scaleOnly||scaleSet.has(n%12));}
  if(!candidates.length)throw new Error('選択した条件では音を生成できません');
  const harmonic=['harmonic','accompanied'].includes(el.melodyComposition?.value);
  const rhythm=el.melodyRhythm?.value==='musical'?melodicRhythm(count):null;
  if(rhythm)count=rhythm.length;const harmony=harmonic?melodyHarmony(scaleName,key,count,rhythm):null;
  const notes=[];
  const phrasePlan=melodicPhrasePlan(rhythm,scaleName,key);
  let previous=continuity?previousMelodyEnding:anchor;
  for(let i=0;i<count;i++){
    let choices=candidates;
    if(natural||continuity){
      const maxLeap=i===0&&continuity?7:i===0?7:5;
      const near=candidates.filter(n=>Math.abs(n-previous)<=maxLeap);
      if(near.length)choices=near;
    }
    // End a phrase on stable degrees when available, but do not force large jumps.
    const isEnd=!!rhythm?.[i]?.phraseEnd||(!rhythm&&i===count-1);
    const chosen=(natural||continuity||harmonic)?weightedChoice(choices,n=>{
      const delta=Math.abs(n-previous);
      const stable=[0,4,7].includes((n-key+120)%12);
      const step=delta<=2?3:delta<=4?1.8:0.65;
      const close=1/(1+delta*0.45);
      const repeat=n===previous?0.3:1;
      const plan=phrasePlan?.[i];
      const theme=plan?songPhraseThemes.get(plan.themeKey)?.get(plan.themeSlot):undefined;
      const target=plan?phraseMotionTarget(rhythm[i],key,anchor)+(plan.motifOffset*.5):anchor;
      // A returning chorus should sound related, but chords can reharmonize the motif.
      const themeTarget=theme===undefined?target:anchor+theme;
      const motifWeight=(plan?Math.exp(-Math.abs(n-themeTarget)*(musicGoal()==='song'?0.48:0.07)):1)*melodyVariantWeight(i,plan,previous,n,anchor);
      const answerPhrase=plan&&songSectionAt(plan.bar).offset%8>=4;
      const replyWeight=answerPhrase&&plan?.phraseEnd?([0,3,4,7].includes((n-key+120)%12)?3.5:.45):1;
      const expressiveRange=plan?.energy>0.8?1.15:1;
      const arcGoal=plan?.bar!==undefined?phraseTension(plan.bar):.5;
      const peakBias=plan?Math.exp(-Math.abs(n-(anchor+(arcGoal-.4)*7))*.06):1;
      const chord=harmony?.[i]?.notes;
      const strong=rhythm?rhythm[i].beatPosition<0.01||Math.abs(rhythm[i].beatPosition-2)<0.01:i%4===0;
      const chordWeight=chord?(chord.has(n%12)?(strong?7:3):
        [...chord].some(pc=>pitchDistance(pc,n%12)<=2)?(strong?0.48:1.35):(strong?0.13:0.45)):1;
      return step*close*repeat*(isEnd&&stable?1.7:1)*chordWeight*motifWeight*cadenceWeight(n,key,harmony?.[i],rhythm?.[i],plan)*expressiveRange*peakBias*replyWeight;
    }):pick(choices);
    notes.push(chosen);
    // Store only the first realization of a motif; subsequent phrases reuse it
    // softly so harmony, voice leading and the selected instrument still matter.
    const plan=phrasePlan?.[i];
    if(plan&&musicGoal()==='song'){
      if(!songPhraseThemes.has(plan.themeKey))songPhraseThemes.set(plan.themeKey,new Map());
      const phrase=songPhraseThemes.get(plan.themeKey);
      if(!phrase.has(plan.themeSlot))phrase.set(plan.themeSlot,chosen-anchor);
      if(songPhraseThemes.size>24)songPhraseThemes.delete(songPhraseThemes.keys().next().value);
    }
    previous=chosen;
  }
  // Joint melodic/harmonic review: on strong beats prefer chord tones, but keep
  // passing tones and neighboring tones on weak beats.
  if(harmony&&musicGoal()==='song'){
   for(let i=0;i<notes.length;i++){
    const r=rhythm?.[i],ch=harmony[i];if(!ch?.notes)continue;
    const strong=!r||r.beatPosition<.01||r.phraseEnd;
    if(!strong||ch.notes.has(notes[i]%12))continue;
    const before=melodyFitness(notes,rhythm,harmony,key);
    const alternatives=candidates.filter(n=>ch.notes.has(n%12)&&Math.abs(n-notes[i])<=3&&(!i||Math.abs(n-notes[i-1])<=7));
    if(!alternatives.length)continue;
    const old=notes[i];notes[i]=alternatives.reduce((a,b)=>Math.abs(a-old)<=Math.abs(b-old)?a:b);
    if(melodyFitness(notes,rhythm,harmony,key)<before)notes[i]=old;
   }
  }
  // Local self-review: repair only conspicuous leaps/clashes without replacing the motif.
  if(musicGoal()==='song'&&notes.length>2){
   const before=melodyFitness(notes,rhythm,harmony,key);
   for(let i=1;i<notes.length-1;i++){
    const old=notes[i],prev=notes[i-1],next=notes[i+1];
    if(Math.abs(old-prev)<=8&&Math.abs(next-old)<=8)continue;
    const options=candidates.filter(n=>Math.abs(n-prev)<=5&&Math.abs(n-next)<=7&&(!harmony?.[i]||harmony[i].notes.has(n%12)));
    if(!options.length)continue;
    const proposal=options.reduce((a,b)=>Math.abs(a-(prev+next)/2)<=Math.abs(b-(prev+next)/2)?a:b);
    notes[i]=proposal;
    if(melodyFitness(notes,rhythm,harmony,key)<before)notes[i]=old;
   }
  }
  // Phrase-level audit: retain only locally beneficial repairs, preserving the theme.
  if(musicGoal()==='song'&&harmony&&arrangementQuality({notes,rhythm,harmony})>5){
   for(let i=1;i<notes.length-1;i++){
    const old=notes[i],before=melodyFitness(notes,rhythm,harmony,key);
    const options=candidates.filter(n=>Math.abs(n-notes[i-1])<=6&&Math.abs(n-notes[i+1])<=7&&harmony[i]?.notes?.has(n%12));
    for(const n of options){notes[i]=n;if(melodyFitness(notes,rhythm,harmony,key)>before+1)break;notes[i]=old;}
   }
  }
  // Compare several nearby melodic alternatives in the context of the whole phrase.
  const optimized=optimizePhraseCandidates(notes,candidates,rhythm,harmony,key);
  for(let i=0;i<notes.length;i++)notes[i]=optimized[i];
  const chordInfos=harmony?harmony.map((chord,i)=>chordInfo(chord,key,scaleName,rhythm?.[i]?.measure??Math.floor(i/4))):null;
  const progressionName=harmony?.[0]?.progressionName||'自動生成';
  return {inst,notes,key,scaleName,rhythm,harmony,accompanied,chordInfos,progressionName,phrasePlan};
}

const EXTENDED_PROGRESSION_LIBRARY=[
 {name:'王道進行（7th）',genre:'J-POP',mode:'major',chords:[[5,'Major7','IVmaj7','よん'],[7,'7th','V7','ご'],[4,'Minor7','iiim7','さん'],[9,'Minor7','vim7','ろく']]},
 {name:'カノン進行（拡張）',genre:'J-POP',mode:'major',chords:[[0,'Major','I','いち'],[7,'Major','V','ご'],[9,'Minor7','vim7','ろく'],[4,'Minor','iii','さん'],[5,'Major7','IVmaj7','よん'],[0,'Major','I','いち'],[5,'Major7','IVmaj7','よん'],[7,'7th','V7','ご']]},
 {name:'I–V–vi–IV（拡張）',genre:'ロック',mode:'major',chords:[[0,'Major','I','いち'],[7,'Major','V','ご'],[9,'Minor7','vim7','ろく'],[5,'Major7','IVmaj7','よん']]},
 {name:'ii–V–I–vi',genre:'ジャズ',mode:'major',chords:[[2,'Minor7','iim7','に'],[7,'7th','V7','ご'],[0,'Major7','Imaj7','いち'],[9,'Minor7','vim7','ろく']]},
 {name:'I–vi–ii–V',genre:'ジャズ',mode:'major',chords:[[0,'Major7','Imaj7','いち'],[9,'Minor7','vim7','ろく'],[2,'Minor7','iim7','に'],[7,'7th','V7','ご']]},
 {name:'ジャズ循環（セカンダリードミナント）',genre:'ジャズ',mode:'major',chords:[[0,'Major7','Imaj7','いち'],[9,'7th','VI7','ろく'],[2,'Minor7','iim7','に'],[7,'7th','V7','ご']]},
 {name:'マイナー ii–V–i',genre:'マイナー',mode:'minor',chords:[[2,'HalfDim7','iiø7','に'],[7,'7th','V7','ご'],[0,'Minor7','im7','いち'],[0,'Minor','i','いち']]},
 {name:'アンダルシア（7th）',genre:'マイナー',mode:'minor',chords:[[0,'Minor','i','いち'],[10,'Major','VII','なな'],[8,'Major7','VImaj7','ろく'],[7,'7th','V7','ご']]},
 {name:'借用和音（iv–I）',genre:'J-POP',mode:'major',chords:[[0,'Major7','Imaj7','いち'],[5,'Major7','IVmaj7','よん'],[5,'Minor','iv','よん'],[0,'Major','I','いち']]},
 {name:'sus4解決',genre:'ロック',mode:'major',chords:[[0,'Major','I','いち'],[7,'sus4','Vsus4','ご'],[7,'7th','V7','ご'],[0,'Major','I','いち']]}
];
const THEORY_PROGRESSIONS=[
 {name:'セカンダリードミナント（V/ii）',genre:'ジャズ',mode:'major',chords:[[0,'Major7','Imaj7','いち'],[9,'7th','V7/ii','ご'],[2,'Minor7','ii7','に'],[7,'7th','V7','ご']]},
 {name:'セカンダリードミナント（V/V）',genre:'J-POP',mode:'major',chords:[[0,'Major','I','いち'],[2,'7th','V7/V','ご'],[7,'7th','V7','ご'],[0,'Major','I','いち']]},
 {name:'バックドア進行',genre:'ジャズ',mode:'major',chords:[[0,'Major7','Imaj7','いち'],[5,'Minor7','ivm7','よん'],[10,'7th','♭VII7','なな'],[0,'Major7','Imaj7','いち']]},
 {name:'マイナー借用和音（iv）',genre:'J-POP',mode:'major',chords:[[0,'Major','I','いち'],[5,'Major','IV','よん'],[5,'Minor','iv','よん'],[0,'Major','I','いち']]},
 {name:'♭VI–♭VII–I',genre:'ロック',mode:'major',chords:[[0,'Major','I','いち'],[8,'Major','♭VI','ろく'],[10,'Major','♭VII','なな'],[0,'Major','I','いち']]},
 {name:'クリシェ（下降ベース）',genre:'J-POP',mode:'major',chords:[[0,'Major','I','いち'],[4,'Minor','iii','さん'],[9,'Minor7','vi7','ろく'],[5,'Minor','iv','よん'],[7,'7th','V7','ご']]},
 {name:'循環（III7–VI7–II7–V7）',genre:'ジャズ',mode:'major',chords:[[4,'7th','III7','さん'],[9,'7th','VI7','ろく'],[2,'7th','II7','に'],[7,'7th','V7','ご']]},
 {name:'マイナー属七（V7–i）',genre:'マイナー',mode:'minor',chords:[[0,'Minor','i','いち'],[5,'Minor','iv','よん'],[7,'7th','V7','ご'],[0,'Minor','i','いち']]},
 {name:'マイナー ♭VI–V7–i',genre:'マイナー',mode:'minor',chords:[[0,'Minor','i','いち'],[8,'Major7','♭VImaj7','ろく'],[7,'7th','V7','ご'],[0,'Minor','i','いち']]}
];
function chooseTheoryProgression(genre){
 const base=[...D.PROGRESSIONS,...EXTENDED_PROGRESSION_LIBRARY];
 const eligible=[...base,...THEORY_PROGRESSIONS].filter(p=>genre==='すべて'||p.genre===genre);
 if(!eligible.length)throw new Error('選択ジャンルにコード進行がありません');
 // Chromatic color is common, but not every progression needs borrowed chords.
 return weightedChoice(eligible,p=>THEORY_PROGRESSIONS.includes(p)?3.2:EXTENDED_PROGRESSION_LIBRARY.includes(p)?1.3:0.7);
}
function generateProgressionChord(data,inst,key,inversionMode='root',previous=null){
 const [offset,type,degree,spoken]=data,root=(key+offset)%12,intervals=D.CHORD_TYPES[type];
 if(!intervals)throw new Error('未対応のコード種類：'+type);
 const options=[];
 for(let inv=0;inv<(inversionMode==='root'?1:intervals.length);inv++){
  try{
   if(inst.guitarVoicing){
    const list=guitarVoicings(root,intervals,inv,inst,12);
    for(const v of list.slice(0,30))options.push({name:type,root,inversion:inv,notes:v.notes,frets:v.frets,degree,spoken});
   }else options.push({name:type,root,inversion:inv,notes:genericChordNotes(root,intervals,inst,inv),frets:null,degree,spoken});
  }catch(_){}
 }
 if(!options.length)throw new Error('コードを配置できません');
 if(inversionMode==='root'||inversionMode==='random'||!previous)return pick(options);
 const score=c=>{
  const prev=previous.notes,notes=c.notes;
  return Math.abs(notes[0]-prev[0])*1.8+notes.reduce((sum,n)=>sum+Math.min(...prev.map(p=>Math.abs(n-p))),0)+Math.abs(notes.reduce((a,b)=>a+b,0)/notes.length-prev.reduce((a,b)=>a+b,0)/prev.length);
 };
 return options.sort((a,b)=>score(a)-score(b))[0];
}
async function playSingleFor(inst,note,ms,token,velocityOffset=0){if(token!==runToken)return;selectPreset(inst);await audioContext.resume();noteOn(note,velocityOffset);await sleep(ms);if(token===runToken)noteOff(note);}
async function playChordFor(inst,chord,ms,token,mode,displayTitle){if(token!==runToken)return;selectPreset(inst);await audioContext.resume();const notes=chord.notes;if((inst.family==='mono'||inst.guitarVoicing)&&!chord.frets){const each=Math.max(140,Math.min(320,ms/Math.max(1,notes.length)));for(let i=0;i<notes.length;i++){if(token!==runToken)return;if(mode!=='3')setChordDisplay(chord,inst,i,displayTitle||'アルペジオ再生中');noteOn(notes[i]);await sleep(each);noteOff(notes[i]);if(i<notes.length-1)await sleep(45);}return;}if(chord.frets){for(let i=0;i<notes.length;i++){if(token!==runToken)return;if(mode!=='3')setChordDisplay(chord,inst,i,'コードをストローク中');noteOn(notes[i]);await sleep(28);}await sleep(ms);if(token===runToken)stopAllNotes();return;}for(const n of notes)noteOn(n);await sleep(ms);if(token===runToken)stopAllNotes();}
function requestWakeLock(){if(!('wakeLock'in navigator))return;navigator.wakeLock.request('screen').then(x=>{wakeLock=x;x.addEventListener('release',()=>wakeLock=null);}).catch(()=>{});}
async function releaseWakeLock(){if(wakeLock){try{await wakeLock.release();}catch(_){}wakeLock=null;}}
function configureIOSAudio(){try{if(navigator.audioSession)navigator.audioSession.type='playback';}catch(_){}}
function primeSpeech(){if(!('speechSynthesis'in window))return;try{const s=window.speechSynthesis,u=new SpeechSynthesisUtterance('あ');u.lang='ja-JP';u.volume=0.01;s.cancel();s.speak(u);speechPrimePromise=new Promise(resolve=>{let done=false;const finish=()=>{if(done)return;done=true;clearTimeout(t);resolve();};u.onend=finish;u.onerror=finish;const t=setTimeout(finish,1500);});}catch(_){speechPrimePromise=Promise.resolve();}}
function formatRemaining(ms){const s=Math.max(0,Math.ceil(ms/1000));return `${String(Math.floor(s/60)).padStart(2,'0')}:${String(s%60).padStart(2,'0')}`;}
function updateTimer(){const left=endAt-Date.now();el.remaining.textContent='残り時間：'+formatRemaining(left);if(left<=0&&playing)stopSession('時間終了');}
async function runSingle(token){const q=generateSingle();setDisplayLines([noteName(q.note)],q.inst,'単音を再生中');await playSingleFor(q.inst,q.note,durationSec*1000,token);if(token!==runToken)return;await speakNotes([q.note],'0');await speakInstrument(q.inst,'0');if(token===runToken)await sleep(questionGapSec*1000);}
async function runChord(token){let inst=null,chord=null;for(const candidate of selectedInstrumentPool().filter(x=>{try{const [a,b]=getSelectedRange(x);return chordEligible(x)&&b-a>=12;}catch(_){return false;}}).sort(()=>Math.random()-0.5)){try{chord=generateChord(candidate);inst=candidate;break;}catch(_){}}if(!inst)throw new Error('コードを生成できる楽器がありません');setChordDisplay(chord,inst,-1,'コード再生中');await playChordFor(inst,chord,durationSec*1000,token,'1');if(token!==runToken)return;const info=speechLang('1','info')==='en-US'?chordEnglish(chord):chordJapanese(chord);await speakPart('1','info',info);if(chord.inversion>0&&speechEnabled('1','inversion'))await speak(inversionSpeech(chord.inversion,'1'),speechLang('1','inversion'));await speakNotes(chord.notes,'1');await speakInstrument(inst,'1');if(token===runToken)await sleep(questionGapSec*1000);}
async function runInterval(token){const q=generateInterval(),notes=[q.first,q.second],lang=speechLang('2','info');for(let i=0;i<2;i++){setSequenceDisplay('音程',notes,i,q.inst,`音程再生中（${i+1}音目）`);await playSingleFor(q.inst,notes[i],durationSec*1000,token);if(token!==runToken)return;if(i===0)await sleep(soundGapSec*1000);}if(token!==runToken)return;const intervalJa=D.INTERVALS[String(q.gap)]||`${q.gap}半音`;const intervalEn=intervalName(q.gap,'en-US');setSequenceDisplay(`${intervalJa}（${q.direction}）`,notes,1,q.inst,'音程の問題が終了');const info=intervalName(q.gap,lang)+(lang==='en-US'?(q.direction==='上昇'?' ascending':' descending'):(q.direction==='上昇'?'上昇':'下降'));await speakPart('2','info',info);await speakNotes(notes,'2');await speakInstrument(q.inst,'2');if(token===runToken)await sleep(questionGapSec*1000);}
async function runMelody(token){
  const m=await nextComposedMelody(token);
  if(token!==runToken)return;
  if(!m.arrangementPlan)prearrangeMelody(m,arrangementSelections());
  playbackBar=m.rhythm?.[0]?.measure??songMeasure;
  updateMelodyMix();
  displayMelodyQuestion(m);
  const tempo=Math.max(40,Math.min(240,Number(el.melodyTempo?.value)||100));
  const beatMs=track14?60000/track14.bpm:60000/(musicGoal()==='song'?Math.max(40,Math.min(240,tempo*personalityAt(m.rhythm?.[0]?.measure??songMeasure).tempo)):tempo);
  let accompaniment=[];
  const backing=arrangementInstrument('backingInstrument',m.inst)||m.inst;
  const leadLayers=['leadLayer1','leadLayer2'].map(id=>[id,arrangementInstrument(id)]).filter(x=>x[1]);
  const backingLayers=['backingLayer1','backingLayer2'].map(id=>[id,arrangementInstrument(id)]).filter(x=>x[1]);
  for(const [id,inst] of [...leadLayers,...backingLayers])setChannelInstrument(ARRANGEMENT_CHANNELS[id],inst);
  updateArrangementVolumes();
  try{for(let i=0;i<m.notes.length;i++){
    const rhythm=m.rhythm?.[i];
    playbackBar=rhythm?.measure??playbackBar;
    const label=rhythm?` / ${Number(rhythm.beats.toFixed(3))}拍${rhythm.rest?' ＋休符'+rhythm.rest+'拍':''}`:'';
    updateMelodyQuestion(m,i,label);
    currentMelodyEnergy=musicalEnergy(rhythm?.measure??Math.floor(i/4));
    const slotMs=rhythm?rhythm.beats*beatMs:null;
    const ending=rhythm&&musicGoal()==='song'&&songEnding(rhythm.measure);
    const leadRest=rhythm&&expressiveRest(rhythm,rhythm.measure,'lead');
    const soundMs=slotMs?Math.max(35,slotMs*rhythm.articulation*(ending?.88:1)):durationSec*1000;
    if(m.backing19)playBacking19(m,i,token);
    else if(m.accompanied&&(i===0||(m.basicPlan&&m.basicPlan[i].join()!==m.basicPlan[i-1]?.join())||(m.harmony?.[i]?.harmonicStep!==m.harmony?.[i-1]?.harmonicStep)||((rhythm?.beatPosition===0)&&rhythm.measure%4===0)||((rhythm?.beatPosition!==undefined)&&grooveAccent(rhythm.measure,rhythm.beatPosition)&&rhythm.beatPosition>0&&instrumentRole(backing)!=='sustain'))){
      for(const n of accompaniment)synth.noteOff(1,n);
      accompaniment=[];
      if(m.harmony?.[i]&&!(musicGoal()==='song'&&rhythm&&songSectionAt(rhythm.measure).offset%8===7&&rhythm.beatPosition>=2)&&(!ending||(m.end14&&i===m.notes.length-1))){
        accompaniment=m.basicPlan?.[i]?.slice()??enhancedVoicing(m.harmony[i],m.notes[i],backing,accompanimentVoicing,rhythm?.measure??0);
        if(accompaniment.length)accompanimentVoicing=[...accompaniment];
        if(accompaniment.length){
          setAccompanimentPreset(backing);updateMelodyMix();
          const style=accompanimentStyle(rhythm?.section??0);
          const notes=style==='broken'?[...accompaniment].reverse():accompaniment;
          if(style==='block'){for(const n of notes)synth.noteOn(1,n,performanceVelocity(48+currentMelodyEnergy*12,rhythm?.measure??0,rhythm?.beatPosition??0,'backing'));}
          else if(style==='bass'){
            synth.noteOn(1,notes[0],70);
            for(const n of notes.slice(1))synth.noteOn(1,n,48);
          }else{
            // schedule notes within a beat; each note belongs to the accompaniment channel
            const delay=style==='arpeggio'?Math.min(180,beatMs/3):Math.min(260,beatMs/2);
            for(let j=0;j<notes.length;j++){
              const n=notes[j];
              if(j===0)synth.noteOn(1,n,62);
              else arrangementEvent(j*delay,token,()=>synth.noteOn(1,n,57));
            }
          }
        }
      }
    }
    // All extra instruments are scheduled independently from the main melody.
    for(const event of m.arrangementPlan?.[i]||[]){
      playArrangementEvent(event.id,event.inst,event.pitches,event.velocity,event.holdMs,token,event.delayMs);
    }
    if(!leadRest||track14)await playSingleFor(m.inst,m.notes[i],soundMs,token,rhythm?.lyricalVelocity??0);
    else await sleep(soundMs);
    if(rhythm&&musicGoal()==='song'&&newSongBoundary(rhythm.measure+1)&&rhythm.phraseEnd&&i===m.notes.length-1){
      clearArrangement();for(const n of accompaniment)synth.noteOff(1,n);accompaniment=[];
      await sleep(Math.min(1800,beatMs*1.7));
    }
    if(token!==runToken)return;
    if(i<m.notes.length-1||track14){
      const gap=rhythm?Math.max(0,slotMs-soundMs)+(rhythm.rest*beatMs)+(rhythm.phraseEnd&&!track14?beatMs*0.5:0):soundGapSec*1000;
      await sleep(gap);
    }
  }
  }finally{for(const n of accompaniment)synth.noteOff(1,n);clearArrangement(!!m.backing19&&!m.end14&&token===runToken); }
  if(token!==runToken)return;
  previousMelodyEnding=m.notes[m.notes.length-1];
  const keyLang=speechLang('4','key'),keyText=pitchText(m.key,keyLang),scale=(keyLang==='en-US'?D.SCALE_ENGLISH_NAMES:D.SCALE_JAPANESE_NAMES)[m.scaleName]||m.scaleName;
  await speakPart('4','key',keyText+' '+scale);
  await speakNotes(m.notes,'4');await speakInstrument(m.inst,'4');
  if(token===runToken&&!track14)await sleep(questionGapSec*1000);
}
async function runProgression(token){
  const genre=el.genre.value,source=el.progressionSource?.value||'legacy';
  const library=source==='extended'?EXTENDED_PROGRESSION_LIBRARY:source==='all'?[...D.PROGRESSIONS,...EXTENDED_PROGRESSION_LIBRARY]:D.PROGRESSIONS;
  const choices=library.filter(p=>genre==='すべて'||p.genre===genre);
  if(!choices.length&&source!=='theory')throw new Error('選択されたジャンルに進行がありません');
  const progression=source==='theory'?chooseTheoryProgression(genre):pick(choices),key=el.progressionKeyMode.value==='0'?Math.floor(Math.random()*12):parseKeyText(el.progressionKey.value);
  const candidates=selectedInstrumentPool().filter(x=>{try{const [a,b]=getSelectedRange(x);return chordEligible(x)&&b-a>=12;}catch(_){return false;}}).sort(()=>Math.random()-0.5);let inst=null,chords=null;for(const candidate of candidates){try{const generated=[];for(const data of progression.chords)generated.push(generateProgressionChord(data,candidate,key,el.progressionInversion?.value||'root',generated.at(-1)));inst=candidate;chords=generated;break;}catch(_){}}if(!inst)throw new Error('このコード進行を演奏できる楽器が選択されていません');
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
function validateSettings(){const minutes=Number(el.minutes.value),duration=Number(el.duration.value),soundGap=Number(el.soundGap.value),questionGap=Number(el.questionGap.value);if(!Number.isFinite(minutes)||minutes<0.1||minutes>600)throw new Error('再生時間は0.1〜600分で指定してください');if(!Number.isFinite(duration)||duration<=0)throw new Error('音の長さは0秒より大きくしてください');if(!Number.isFinite(Number(el.octaveGap.value))||Number(el.octaveGap.value)<0)throw new Error('音名とオクターブ番号の間隔は0秒以上にしてください');if(!Number.isFinite(soundGap)||soundGap<0||!Number.isFinite(questionGap)||questionGap<0)throw new Error('間隔は0秒以上で指定してください');if(!selectedInstrumentPool().some(x=>{try{getSelectedRange(x);return true;}catch(_){return false;}}))throw new Error('選択した音域に対応する楽器がありません');if(['1','3'].includes(el.mode.value)&&!selectedInstrumentPool().some(x=>{try{const [a,b]=getSelectedRange(x);return chordEligible(x)&&b-a>=12;}catch(_){return false;}}))throw new Error('コード演奏に対応した楽器を選択してください');if(el.mode.value==='4'&&!selectedInstrumentPool().some(x=>{try{getRangeForMelody(x);return true;}catch(_){return false;}}))throw new Error('選択した楽器とメロディ音域が一致しません');if(el.mode.value==='3'&&el.progressionKeyMode.value==='1')parseKeyText(el.progressionKey.value);if(el.mode.value==='4'&&el.melodyRhythm?.value==='musical'&&(!Number.isFinite(Number(el.melodyTempo.value))||Number(el.melodyTempo.value)<40||Number(el.melodyTempo.value)>240))throw new Error('テンポは40〜240 BPMで指定してください');durationSec=duration;soundGapSec=soundGap;questionGapSec=questionGap;return minutes;}
async function startSession(){if(playing||!soundLoaded)return;configureIOSAudio();if(el.speech.value==='on')primeSpeech();let minutes;try{minutes=validateSettings();}catch(e){el.status.textContent=e.message;return;}requestWakeLock();el.start.disabled=true;el.stop.disabled=true;try{await audioContext.resume();if(el.speech.value==='on')await speechPrimePromise;playing=true;mixTrimV11.fill(1);mixTickV11=0;recurrenceV11.clear();runToken++;const token=runToken;endAt=Date.now()+minutes*60000;previousNote=-1;previousMelodyEnding=null;songHarmony=null;songMeasure=0;track14=null;serial14=0;songRhythmCarry=null;songMotif=null;songMelodyMotifs.clear();songArrangementMotifs.clear();songGrooveMemory.clear();songPhraseThemes.clear();songBassMemory.clear();songSoundIdentity.clear();songBassContour.clear();songPersonality=null;songPersonalityCycle=-1;songPersonalityNextCycle=0;songPersonalityGeneration=0;accompanimentVoicing=null;arrangementVoicing.clear();arrangementMotifPatterns.clear();songInstrumentation.clear();composedSongQueue=[];composedSongCycle=-1;playbackBar=0;el.stop.disabled=false;el.status.textContent='トレーニング中';timerTicker=setInterval(()=>{updateTimer();if(el.mode.value==='4'&&musicGoal()==='song'){monitorMixV10();monitorChannelsV11();}else if(mixGain)mixGain.gain.value=1;},250);updateTimer();sessionLoop(token).catch(e=>{if(token===runToken)stopSession('再生エラー：'+e.message);});}catch(e){el.status.textContent='再生準備エラー：'+e.message;el.start.disabled=false;el.stop.disabled=true;releaseWakeLock();}}
function stopSession(reason='停止しました'){composedSongQueue=[];composedSongCycle=-1;if(!playing&&el.start.disabled===false)return;playing=false;runToken++;clearTimers();releaseWakeLock();if(timerTicker){clearInterval(timerTicker);timerTicker=null;}stopAllNotes();clearArrangement();try{speechSynthesis.cancel();}catch(_){}try{audioContext?.suspend();}catch(_){}el.start.disabled=!soundLoaded;el.stop.disabled=true;el.status.textContent=reason;el.remaining.textContent='残り時間：00:00';if(reason==='時間終了')el.answer.textContent='終了';}

el.instrument.addEventListener('change',()=>{updateSettingsVisibility();updateInstrumentRange();});el.mode.addEventListener('change',updateSettingsVisibility);el.range.addEventListener('change',updateSettingsVisibility);el.melodyKeyMode.addEventListener('change',updateSettingsVisibility);el.melodyScaleMode.addEventListener('change',updateSettingsVisibility);el.melodyCategory.addEventListener('change',updateMelodyScales);el.progressionKeyMode.addEventListener('change',updateSettingsVisibility);for(const [id,output] of [['instrumentVolume','instrumentVolumeValue'],['speechVolume','speechVolumeValue']])el[id].addEventListener('input',()=>$(output).textContent=el[id].value+'%');el.speed.addEventListener('input',()=>el.speedValue.textContent=Number(el.speed.value).toFixed(1));el.start.addEventListener('click',startSession);el.stop.addEventListener('click',()=>stopSession('停止しました'));
window.addEventListener('visibilitychange',()=>{if(document.visibilityState==='visible'&&playing){configureIOSAudio();requestWakeLock();audioContext?.resume().catch(()=>{});}});window.addEventListener('pagehide',()=>{stopSession('停止しました');});

buildInstrumentOptions();buildSpeechSettings();populateSettings();populateArrangementInstruments();updateSettingsVisibility();el.start.disabled=true;el.speedValue.textContent=Number(el.speed.value).toFixed(1);setLoadProgress(0,'音源を読み込んでいます…');loadSoundBank().catch(err=>{setLoadProgress(0,'音源読み込みエラー：'+err.message);el.status.textContent='音源読み込みエラー：'+err.message;el.start.disabled=true;});
