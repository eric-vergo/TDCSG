// Released under Apache 2.0. Authors: Eric Vergo, OpenAI Codex.
// "words" is supplied by BlueprintMain from the figure's Lean declarations.
export function playWords(figure, words) {
  const explorer = figure.querySelector(".pilean-explorer");
  const frames = [...explorer.querySelectorAll(".pilean-explorer-frame svg.pilean-inline-svg")];
  if (frames.length !== words.length) return;
  const reduced = matchMedia("(prefers-reduced-motion: reduce)");
  const ns = "http://www.w3.org/2000/svg";

  function element(tag, text) {
    const node = document.createElement(tag);
    if (text !== undefined) node.textContent = text;
    return node;
  }

  function svg(tag, attrs) {
    const node = document.createElementNS(ns, tag);
    for (const [key, value] of Object.entries(attrs)) node.setAttribute(key, value);
    return node;
  }

  // Keep the original explorer available with its numbered paths, Lean links and pan/zoom.
  const stills = element("details");
  stills.className = "word-traces";
  stills.append(element("summary", "Inspect the three numbered traces"));
  explorer.before(stills);
  stills.append(explorer);

  function makePlate(frame, word, number) {
    const plate = element("section");
    plate.className = "word-plate";
    plate.setAttribute("aria-label", "Word " + number);
    const header = element("div");
    header.className = "word-heading";
    const link = element("a");
    link.setAttribute("href", frame.querySelector("a.pilean-decl-link").getAttribute("href"));
    link.textContent = "Word " + number;
    const formula = element("span");
    formula.className = "word-formula";
    const tokens = word.letters.map(letter => element("i", letter.text));
    formula.append(...tokens);
    header.append(link, formula);

    // Copy only the named PILean objects. Each stop is an actual path from the checked figure.
    const groups = new Map([...frame.querySelectorAll("g > title")].map(title =>
      [title.textContent, title.parentElement]));
    const paths = word.letters.map((_, k) => k === 0 ? "the piece of word " + number :
      "its image after " + k + " letters");
    paths.push("its image after all " + word.letters.length + " letters, on the chord");
    const stops = paths.map(name => groups.get(name).querySelector("path").getAttribute("d"));
    const disks = ["the left circle", "the right circle"];
    const centers = ["the center −1", "the center 1"];
    const scene = svg("svg", {class:"word-scene", viewBox:frame.getAttribute("viewBox"),
      role:"img", "aria-label":"Word " + number + " carries its segment back to the chord."});
    const objects = [...disks, "the lens", "the chord from −E to E", ...centers];
    const classes = ["left-disk","right-disk","lens","chord","left-center","right-center"];
    for (const [index, name] of objects.entries()) {
      const group = groups.get(name).cloneNode(true);
      group.setAttribute("class",classes[index]);
      scene.append(group);
    }
    const pins = centers.map((_, i) => scene.querySelector(i ? ".right-center" : ".left-center"));
    const origin = svg("path",{class:"word-origin",d:stops[0]});
    const segment = svg("path",{class:"word-segment",d:stops[0]});
    const pivot = svg("circle",{class:"word-pivot",r:9});
    scene.append(origin, segment, pivot);

    const contacts = [];
    for (const [name, group] of groups) {
      const match = /^an end on the (left|right) circle before letter (\d+)/.exec(name);
      if (!match) continue;
      const mark = group.cloneNode(true);
      mark.setAttribute("class","word-contact");
      scene.append(mark);
      contacts.push({step:Number(match[2])-1, mark});
    }

    const scale = element("div");
    scale.className = "word-scale";
    const ruler = element("div");
    ruler.className = "word-ruler";
    function interval(bounds, text) {
      const strip = element("span",text);
      strip.style.left = ((1 + bounds[0])*50) + "%";
      strip.style.width = ((bounds[1]-bounds[0])*50) + "%";
      ruler.append(strip);
      return strip;
    }
    const source = interval(word.start, "start");
    source.className = "word-source";
    const landing = interval(word.landing, "landing");
    landing.className = "word-landing";
    const limits = element("div");
    limits.className = "word-limits";
    for (const text of ["−1","0","1"]) limits.append(element("span",text));
    scale.append(element("b","Position on the chord"), ruler, limits);

    const controls = element("div");
    controls.className = "word-controls";
    const toggle = element("button","Pause"), replay = element("button","Replay");
    toggle.type = replay.type = "button";
    const status = element("span");
    controls.append(toggle,replay,status);
    const note = element("p", [
      "Follow the short piece from the left end of the chord. Five inverse turns carry it to the right.",
      "The second piece takes five clockwise turns. It lands beside the first piece with the same shift.",
      "The longest piece changes direction after the third turn. Its landing wraps around the end of the interval."
    ][number-1]);
    note.className = "word-note";
    plate.append(header,scene,scale,controls,note);
    stills.before(plate);

    const pivots = pins.map((pin,i) => {
      const box = pin.getBBox();
      const x = box.x+box.width/2, y = box.y+box.height/2;
      const text = svg("text",{x:x+(i ? -17 : 17),y:y+(i ? 22 : -12),"text-anchor":"middle"});
      text.textContent = i ? "+1" : "−1";
      scene.append(text);
      return [x,y];
    });
    const chord = scene.querySelector(".chord path");
    for (const [end, name] of [[0,"−E"], [1,"E"]]) {
      const pt = chord.getPointAtLength(end*chord.getTotalLength());
      const label = svg("text",{x:pt.x+(end ? 11 : -12),y:pt.y+(end ? -8 : 17),"text-anchor":"middle"});
      label.textContent = name;
      scene.append(label);
    }
    // Fit the stationary disks, excluding the baked-in caption below the original drawing.
    const boxes = [".left-disk",".right-disk"].map(sel=>scene.querySelector(sel).getBBox());
    const x0 = boxes[0].x-12, y0 = boxes[0].y-12;
    scene.setAttribute("viewBox", [x0,y0,boxes[1].x+boxes[1].width-x0+12,boxes[0].height+24].join(" "));

    const sequence = element("ol");
    sequence.className = "word-stills";
    word.letters.forEach((letter, k) => {
      const item = element("li");
      const picture = svg("svg",{viewBox:scene.getAttribute("viewBox"),"aria-hidden":"true"});
      for(const selector of [".left-disk",".right-disk",".chord"])
        picture.append(scene.querySelector(selector).cloneNode(true));
      picture.append(svg("path",{class:"word-origin",d:stops[k]}),
        svg("path",{class:"word-segment",d:stops[k+1]}));
      item.append(element("span",(k+1)+". "+letter.text+" · "+(letter.left?"left":"right")),picture);
      sequence.append(item);
    });
    plate.append(sequence);

    const turn = 1350, lead = 700, end = lead + turn*word.letters.length, period = end+1800;
    let time = 0, previous = null, request = 0, visible = false, paused = false, lastStep = -2;
    function draw() {
      const done = time >= end, raw = Math.max(0,(time-lead)/turn);
      const k = done ? word.letters.length : Math.floor(raw);
      if(lastStep !== k) {
        lastStep = k;
        segment.setAttribute("d",stops[k]);
        tokens.forEach((token,i)=>token.classList.toggle("current",i===k));
        landing.hidden = !done;
        for (const contact of contacts) contact.mark.style.display = contact.step === k ? "" : "none";
        scene.dataset.active = done ? "" : (word.letters[k].left ? "left" : "right");
        pivot.style.display = done ? "none" : "";
        status.textContent = done ? "Back on the chord" :
          "Turn "+(k+1)+" of "+word.letters.length+" · "+(word.letters[k].left ? "left disk" : "right disk");
      }
      if(done) {segment.removeAttribute("transform");return;}
      const letter = word.letters[k], [cx,cy] = pivots[letter.left ? 0 : 1];
      const u = Math.min(1,(raw-k)/0.87);
      // SVG y increases downwards, so a mathematical counterclockwise turn is negative.
      const angle = (letter.inverse ? -72 : 72)*u*u*(3-2*u);
      const rotation = "rotate("+angle+" "+cx+" "+cy+")";
      segment.setAttribute("transform",rotation);
      for (const contact of contacts)
        if (contact.step === k) contact.mark.setAttribute("transform",rotation);
      pivot.setAttribute("cx",cx); pivot.setAttribute("cy",cy);
    }
    function tick(now) {
      if(previous !== null) time = (time+now-previous)%period;
      previous = now;
      draw();
      request = requestAnimationFrame(tick);
    }
    function sync() {
      cancelAnimationFrame(request);
      previous = null;
      if(reduced.matches) time = end;
      sequence.hidden = !reduced.matches;
      controls.hidden = reduced.matches;
      toggle.textContent = paused ? "Play" : "Pause";
      draw();
      if(visible && !paused && !reduced.matches && !document.hidden)
        request = requestAnimationFrame(tick);
    }
    toggle.addEventListener("click",()=>{paused=!paused;sync();});
    replay.addEventListener("click",()=>{time=0;paused=false;sync();});
    new IntersectionObserver(([entry])=>{visible=entry.isIntersecting;sync();}).observe(scene);
    reduced.addEventListener("change",sync);
    document.addEventListener("visibilitychange",sync);
    sync();
  }
  frames.forEach((frame,i)=>makePlate(frame,words[i],i+1));
}
