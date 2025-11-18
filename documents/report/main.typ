#import "./lib/template/lib.typ": *
#import "@preview/gruvy:2.1.0": gruvbox, theme-colors, colors
#import "@preview/zebraw:0.5.5": *
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/xarrow:0.3.1": xarrow, xarrowSquiggly, xarrowTwoHead
#import "@preview/theorion:0.4.0": *
#import cosmos.clouds: *
#import cosmos.clouds: render-fn as render-fn-2
#show: show-theorion

#set text(lang: "en")
#let theme = theme-colors.light.hard;
#show: zebraw.with(
    background-color: theme.bg0,
    lang-color: theme-colors.dark.soft.strong.blue,
)
#show: gruvbox.with(
    theme-color: theme,
    accent: theme.strong.blue,
    hl: theme.muted.yellow,
    print: true,
)
#show ref: set text(fill: theme.fg1)
#show: ilm.with(
  title: [Zero to Lasso],
  author: "Rasmus Kirk Jakobsen",
  date: datetime.today(),
  abstract: text(size: 10pt, [
    Lorem ipsum dolor sit amet, consectetur adipiscing elit. Donec sodales commodo
    neque consectetur interdum. In nisi enim, consequat quis mauris sit amet,
    porta auctor augue. Cras accumsan id libero id pulvinar. Pellentesque semper,
    elit a pretium sollicitudin, elit quam pulvinar velit, quis ultrices nisl
    felis nec nisi. Nam placerat dolor elit, tincidunt condimentum justo consequat
    sed.

    Etiam sed porttitor nulla. Aliquam condimentum lacinia dapibus. Sed rutrum
    pulvinar lectus ac fringilla. Cras nibh nibh, tristique at arcu commodo,
    semper facilisis urna. Sed euismod pellentesque mauris, a vehicula urna
    pellentesque id. Nam tellus felis, ultricies eget nibh in, euismod suscipit
    lacus. Pellentesque scelerisque, augue ac auctor viverra, orci purus viverra
    odio, vitae iaculis est leo ac ante. Vivamus commodo tellus ut nisi vulputate,
    eget cursus diam fringilla. Fusce tempor velit eget libero maximus feugiat.
  ]),
  date-format: "[year repr:full]-[month padding:zero]-[day padding:zero]",
  bibliography: bibliography("refs.bib"),
  figure-index: (enabled: true),
  table-index: (enabled: true),
  listing-index: (enabled: true),
)
#let remark = remark.with(fill: theme.muted.blue)
#let tip-box = tip-box.with(fill: theme.strong.green)
#let caution-box = caution-box.with(fill: theme.muted.red)
#let warning-box = warning-box.with(fill: theme.muted.yellow)
#let theorem = theorem.with(fill: theme.muted.blue.lighten(80%))
#let lemma = lemma.with(fill: theme-colors.dark.soft.strong.blue.lighten(80%))
#let (example-counter, example-box, example, show-example) = make-frame(
  "theorem",
  theorion-i18n-map.at("example"),
  counter: none,
  render: render-fn-2.with(fill: theme.bg0.lighten(30%)),
)
#let todo-box = note-box.with(
  fill: theme.strong.aqua,
  title: "To-do",
  icon-name: "pencil",
)

// Math
#let meq = math.eq.quest;
#let wildcard = underline("  ")
#let prover = math.cal("P")
#let verifier = math.cal("V")
#let circuit = math.cal("C")
#let bits = math.bb("B")
#let Fb = math.bb("F")
#let inrand = $attach(in, br: R)$
#let vec(body) = $bold(body)$

= Sumcheck

$ H := sum_(b_1 in bits) sum_(b_2 in bits) dots sum_(b_v in bits) g(b_1, dots, b_v) $

#align(center)[
  #set math.equation(numbering: none)
  #set text(10pt)
  #let w = 0.7
  #diagram({
    let (A, B) = ((0, 0), (3, 0))
    node(A, text(size: 12pt, weight: "black", "Prover"))
    node(B, text(size: 12pt, weight: "black", "Verifier"))

    // -------------------- Round 1 -------------------- //
    let (A, B, C) = ((0, w), (1.5, w), (3, w))
    node(B, text(size: 12pt, weight: "black", "Round 1"))
    edge(A, B, "=")
    edge(B, C, "=")

    let (A, B) = ((0, 2*w), (3, 2*w))
    node(A, move(dy: .35em, $ g_1(X) := limits(sum)_(x_(2:v) in bits^(v-1)) g(X, x_(2:v))$))
    node(B, $ H meq g_1(0) + g_1(1)$)
    edge(A, B, "->", $H, g_1(X)$)

    let (A, B) = ((0, 3*w), (3, 3*w))
    node(A, )
    node(B, $ deg(g_1) meq deg_1(g) $)

    let (A, B) = ((0, 4*w), (3, 4*w))
    node(A, "")
    node(B, $ r_1 inrand Fb $)
    edge(B, A, "->", $r_1$)

    // -------------------- Round j -------------------- //
    let (A, B, C) = ((0, 5*w), (1.5, 5*w), (3, 5*w))
    node(B, text(size: 12pt, weight: "black", "Round j"))
    edge(A, B, "=")
    edge(B, C, "=")

    let (A, B) = ((0, 6*w), (3, 6*w))
    node(A, move(dy: .35em, $ g_(j)(X) := limits(sum)_(x_(j+1:v) in bits^(v-j)) g(r_(1:j-1), X, x_(j+1:v))$))
    node(B, $ g_(j-1)(r_(j-1)) meq g_(j)(0) + g_(j)(1)$)
    edge(A, B, "->", $g_(j)(X)$)

    let (A, B) = ((0, 7*w), (3, 7*w))
    node(A, )
    node(B, $ deg(g_j) meq deg_(j)(g) $)

    let (A, B) = ((0, 7*w), (3, 7*w))
    node(A, "")
    node(B, $ r_j inrand Fb $)
    edge(B, A, "->", $r_j$)

    // -------------------- Round v -------------------- //
    let (A, B, C) = ((0, 8*w), (1.5, 8*w), (3, 8*w))
    node(B, text(size: 12pt, weight: "black", "Round v"))
    edge(A, B, "=")
    edge(B, C, "=")

    let (A, B) = ((0, 9*w), (3, 9*w))
    node(A, move(dy: .35em, $ g_(v)(X) := g(r_(1:v-1), X)$))
    node(B, $ g_(v-1)(r_(j-1)) meq g_(v)(0) + g_(v)(1)$)
    edge(A, B, "->", $g_(v)(X)$)

    let (A, B) = ((0, 10*w), (3, 10*w))
    node(A, )
    node(B, $ deg(g_v) meq deg_(v)(g) $)

    let (A, B) = ((0, 11*w), (3, 11*w))
    node(A, "")
    node(B, $ r_v inrand Fb $)

    let (A, B) = ((0, 12*w), (3, 12*w))
    node(A, "")
    node(B, $ g_(v)(r_v) meq g(r_(1:v)) $)
  })
]

= GKR

Given a circuit $circuit$, with $d$ layers, $n$ inputs and $m$ outputs,
a prover ($prover$) wishes to prove to a verifier ($verifier$) a specific
input $vec(w) in bits^n$ applied to $circuit$ produces some output $vec(o)
in bits^m$. To do this, we can leverage the sumcheck protocol, defined earlier.

#figure(
  align(center)[
    #set math.equation(numbering: none)
    #set text(10pt)
    #let w = 0.8
    #let h = 0.8
    #diagram(
      node-stroke: 1pt,
      {
        let N00 = (3*w, 0*h)
        let (N10, N11) = ((1*w, 1*h), (5*w, 1*h))
        let (N20, N21, N22, N23) = (
          (0*w, 2*h),
          (2*w, 2*h),
          (4*w, 2*h),
          (6*w, 2*h),
        )
        let (N30, N31, N32, N33) = (
          (0*w, 3.5*h),
          (2*w, 3.5*h),
          (4*w, 3.5*h),
          (6*w, 3.5*h),
        )

        // Really hacky centering lol
        node((8.25*w, 0*h), "", stroke: none)
        node((-1.2*w, 0*h), "Layer 0")
        node((-1.2*w, 1*h), "Layer 1")
        node((-1.2*w, 2*h), "Layer 2")
        node((-1.2*w, 3.5*h), "Inputs")
        node(N00, [$times_(0)$], radius: 1.2em)
        node(N10, [$times_(0)$], radius: 1.2em)
        node(N11, [$times_(1)$], radius: 1.2em)
        node(N20, [$times_(00)$], radius: 1.2em)
        node(N21, [$times_(01)$], radius: 1.2em)
        node(N22, [$times_(10)$], radius: 1.2em)
        node(N23, [$times_(11)$], radius: 1.2em)
        node(N30, [$v_1$], radius: 1.2em)
        node(N31, [$v_2$], radius: 1.2em)
        node(N32, [$v_3$], radius: 1.2em)
        node(N33, [$v_4$], radius: 1.2em)
        edge(N10, N00, "-|>")
        edge(N11, N00, "-|>")
        edge(N20, N10, "-|>")
        edge(N21, N10, "-|>")
        edge(N22, N11, "-|>")
        edge(N23, N11, "-|>")
        edge(N30, N20, "-->")
        edge(N31, N21, "-->")
        edge(N32, N22, "-->")
        edge(N33, N23, "-->")
      }
    )
  ],
  caption: text[
    A layered arithmetic circuit for the computation $o_1 = product_(i=1)^k
    a_i$. Each node-label below represents the type of computation and the
    gate-label for the given layer, so $(times_0)$ is a multiplication gate
    with label $0$, for layer $0$. Note that $d = 3$, $n = 4$, $m = 1$
  ],
  // supplement: [Diagram],
) <example_circuit>

// We define the following functions:

// - $"in"_(1,i)(a) ~> b : a in bits^(k_i), b in bits^(k_(i+1))$ which takes the gate-label of a node and gives the gate-label of the left input.
// - $"in"_(2,i)(a) ~> c : a in bits^(k_i), c in bits^(k_(i+1))$ which takes the gate-label of a node and gives the gate-label of the right input.

To represent a layered circuit in a form amenable to the sum check protocol,
we must first provide an adequate polynomial representation of the circuit. We
start with the following three functions:

- $"add"_(i)(a,b,c) in bits^(k_i+2k_(i+1)) -> bits$ which outputs $1$ if and only if gate $a$ is an addition gate and $b$ is the left input and $c$ is the right input of gate $a$.
- $"mul"_(i)(a,b,c) in bits^(k_i+2k_(i+1)) -> bits$ which outputs $1$ if and only if gate $a$ is a multiplication gate and $b$ is the left input and $c$ is the right input of gate $a$.
- $W_(i)(a) in bits^(k_i) -> bits$ which, given the gate-label $a$, outputs the value of node $a$.

#example[
  For @example_circuit $"add"_i, "mul"_i$ would evaluate to the following values:

  #math.equation(
    block: true,
    numbering: none,
    $
      mat(delim: #none, column-gap: #3em, align: #left,
        "mul"_0(0 || 0 || 0) = 1,                      "mul"_1(0 || 00 || 01) = 1;
        "mul"_0(0 || 0 || 1) = 1,                      "mul"_1(1 || 10 || 11) = 1;
        "mul"_0(wildcard || wildcard || wildcard) = 0, "mul"_1(wildcard || wildcard || wildcard) = 0;
        "add"_0(wildcard || wildcard || wildcard) = 0, "add"_0(wildcard || wildcard || wildcard) = 0;
      )
    $
  )
]

We can use the multilinear extensions of $"add"_i$ and $"mul"_i$ to represent $W_(i)$ in a form
that lets us use sumcheck:

$ tilde(W)_(i)(a) = sum_(b,c in bits^(k_(i+1))) tilde("add")_(i)(a,b,c)(tilde(W)_(i+1)(b) + tilde(W)_(i+1)(c)) + tilde("mult")_(i)(a,b,c) dot tilde(W)_(i+1)(b) dot tilde(W)_(i+1)(c) $

#todo-box[
  What is the degree of each $W_(i)$? Is it important?
]

= Other

#lemma[
  #set math.equation(numbering: none)
  $ tilde(W)(z) = sum_(b,c in bits^(k_(i+1))) tilde("add")_(i)(z,b,c)(tilde(W)_(i+1)(b) + tilde(W)_(i+1)(c)) + tilde("mult")_(i)(z,b,c) dot tilde(W)_(i+1)(b) dot tilde(W)_(i+1)(c) $

  Lemma 4.7 in the book.
]

#lemma[
  #set math.equation(numbering: none)
  $ h(a_1, a_2) := sum_(b_1, c_1 in bits^k_(i+1)) g(a_1, a_2, b_1, c_1) $

  where

  $ tilde(g)(a_1, a_2, b_1, c_1) = &tilde("add")_(i)(a_1,b_1,c_1)(tilde(W)'_(i+1)(b_1, a_2) + tilde(W)'_(i+1)(c_1, a_2)) + \
                                   &tilde("mult")_(i)(a_1,b_1,c_1) dot tilde(W)'_(i+1)(b_1, a_2) dot tilde(W)_(i+1)(c_1, a_2) $
]

#lemma[
  #set math.equation(numbering: none)
  $ tilde(W)(z) := sum_((a_1, a_2, b_1, c_1) in bits^(k_(i+1) + b + 2k_(i+1))) g^((i))_(z)(a_1, a_2, b_1, c_1) $

  where

  $
  tilde(g)^((i))_(z)(a_1, a_2, b_1, c_1) = tilde(beta)_(k'_i)(z, (a_1, a_2)) dot tilde(g)(a_1, a_2, b_1, c_1)
  $
]

How do we get $S_(i+1)^2$ terms in the first lemma and $S'_(i+1) dot S_(i+1)$ in the second lemma?

- Circuit $C'$ with depth $d$ and size $B dot S$
- With $B = 2^b$ copies of sub-circuit $C$ with depth $d$ and size $S$
- $S_i = 2^(k_i)$
- $S'_i = 2^(k'_i) = 2^(b + k_i)$

#align(center)[
  #set math.equation(numbering: none)
  #set text(10pt)
  #let w = 0.8
  #let h = 0.8
  #diagram(
    node-stroke: 1pt,
    {
      let N00 = (3*w, 0*h)
      let (N10, N11) = ((1*w, 1*h), (5*w, 1*h))
      let (N20, N21, N22, N23) = (
        (0*w, 2*h),
        (2*w, 2*h),
        (4*w, 2*h),
        (6*w, 2*h),
      )
      let (N30, N31, N32, N33) = (
        (0*w, 3.5*h),
        (2*w, 3.5*h),
        (4*w, 3.5*h),
        (6*w, 3.5*h),
      )

      node(N00, [$times_(00)$], radius: 1.2em)
      node(N10, [$times_(10)$], radius: 1.2em)
      node(N11, [$times_(11)$], radius: 1.2em)
      node(N20, [$times_(20)$], radius: 1.2em)
      node(N21, [$times_(21)$], radius: 1.2em)
      node(N22, [$times_(22)$], radius: 1.2em)
      node(N23, [$times_(23)$], radius: 1.2em)
      node(N30, [$a_1$], radius: 1.2em)
      node(N31, [$a_2$], radius: 1.2em)
      node(N32, [$a_3$], radius: 1.2em)
      node(N33, [$a_4$], radius: 1.2em)
      edge(N10, N00, "-|>")
      edge(N11, N00, "-|>")
      edge(N20, N10, "-|>")
      edge(N21, N10, "-|>")
      edge(N22, N11, "-|>")
      edge(N23, N11, "-|>")
      edge(N30, N20, "-|>")
      edge(N31, N21, "-|>")
      edge(N32, N22, "-|>")
      edge(N33, N23, "-|>")
    }
  )
]
