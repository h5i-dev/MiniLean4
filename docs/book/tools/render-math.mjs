// Pre-renders KaTeX at build time. Reads JSON [{tex, display}] on stdin,
// writes JSON [{html, error}] on stdout. Invoked by build.py.
import katex from "./katex.mjs";

let input = "";
process.stdin.setEncoding("utf8");
process.stdin.on("data", (chunk) => (input += chunk));
process.stdin.on("end", () => {
  const items = JSON.parse(input);
  const out = items.map(({ tex, display }) => {
    const opts = {
      displayMode: display,
      throwOnError: true,
      strict: "ignore",
      trust: false,
      output: "htmlAndMathml",
      macros: {
        "\\Sort": "\\mathsf{Sort}\\,",
        "\\imax": "\\mathrm{imax}",
        "\\FV": "\\mathrm{FV}",
        "\\dom": "\\mathrm{dom}",
        "\\Nat": "\\mathsf{Nat}",
        "\\zero": "\\mathsf{zero}",
        "\\suc": "\\mathsf{succ}",
        "\\add": "\\mathsf{add}",
        "\\conv": "\\equiv",
        "\\alphaeq": "=_{\\alpha}",
        "\\betared": "\\to_{\\beta}",
        "\\deltared": "\\to_{\\delta}",
        "\\iotared": "\\to_{\\iota}",
        "\\Infer": "\\mathrm{Infer}",
        "\\Check": "\\mathrm{Check}",
        "\\InferSort": "\\mathrm{InferSort}",
        "\\Freshen": "\\mathrm{Freshen}",
        "\\Whnf": "\\mathrm{Whnf}",
        "\\Normalize": "\\mathrm{Normalize}",
        "\\IsDefEq": "\\mathrm{IsDefEq}",
        "\\rulename": "\;\\text{(#1)}",
        "\\hole": "?_{#1}",
        "\\tPi": "\\Pi(#1{:}#2).\\,#3",
        "\\tLam": "\\lambda(#1{:}#2).\\,#3",
        "\\subst": "#1[#2 \\mapsto #3]",
        "\\db": "\\lfloor #1 \\rfloor_{#2}",
        "\\NatRec": "\\mathsf{Nat.rec}_{#1}",
        "\\Eq": "\\mathsf{Eq}_{#1}",
        "\\refl": "\\mathsf{refl}_{#1}",
        "\\EqRec": "\\mathsf{Eq.ndrec}_{#1}",
        "\\EqRecDep": "\\mathsf{Eq.rec}_{#1}",
        "\\ctxok": "\\vdash #1\;\\mathsf{ok}",
        "\\goal": "\\langle #1 \\vdash #2 : #3 \\rangle",
      },
    };
    try {
      return { html: katex.renderToString(tex, opts), error: null };
    } catch (e) {
      return { html: null, error: String(e.message || e) };
    }
  });
  process.stdout.write(JSON.stringify(out));
});
