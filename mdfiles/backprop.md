---
title: Backpropagation
---

::: {.callout-tip}
## Slides
[Slides](https://docs.google.com/presentation/d/18J7G3N0W3XRP6AX0RHrYfOgiPV_2NHDUMjjXkqI_knc/edit?slide=id.g33a6271ded3_0_0#slide=id.g33a6271ded3_0_0)
::: 

## Problem definitions 


\begin{eqnarray}
  \mathbf{h}_{1} &=& \mathbf{a}[\boldsymbol\beta_{0} +\boldsymbol\Omega_{0}\mathbf{x}]\nonumber \\
  \mathbf{h}_{2} &=& \mathbf{a}[\boldsymbol\beta_{1} +\boldsymbol\Omega_{1}\mathbf{h}_{1}] \nonumber\\
  \mathbf{h}_{3} &=& \mathbf{a}[\boldsymbol\beta_{2} +\boldsymbol\Omega_{2}\mathbf{h}_{2}] \nonumber\\
  \mbox{\bf f}[\mathbf{x},\boldsymbol\phi] &=& \boldsymbol\beta_{3} +\boldsymbol\Omega_{3}\mathbf{h}_{3},
 \end{eqnarray}

\begin{eqnarray}
  L[\boldsymbol\phi]= \sum_{i=1}^{I} \ell_{i}.
 \end{eqnarray}

\begin{eqnarray}\label{eq:train2_sgd}
  \boldsymbol\phi_{t+1}\longleftarrow\boldsymbol\phi_{t} - \alpha \sum_{i\in\mathcal{B}_{t}}\frac{\partial \ell_{i}[\boldsymbol\phi_{t}]}{\partial \boldsymbol\phi},
 \end{eqnarray}

\begin{eqnarray}
  \frac{\partial \ell_{i}}{\partial\boldsymbol\beta_{k}} \quad\quad \mbox{and} \quad\quad \frac{\partial \ell_{i}}{\partial\boldsymbol\Omega_{k}},
 \end{eqnarray}

## Computing derivatives

<img src="assets/Chap07/Train2BPIntuitions.svg" style="filter: invert(1);" width="100%">

Backpropagation forward pass. The goal is to compute the derivatives
of the loss ℓ with respect to each of the weights (arrows) and biases (not shown).
In other words, we want to know how a small change to each parameter will affect
the loss. Each weight multiplies the hidden unit at its source and contributes the
result to the hidden unit at its destination. Consequently, the effects of any small
change to the weight will be scaled by the activation of the source hidden unit.
For example, the blue weight is applied to the second hidden unit at layer 1; if
the activation of this unit doubles, then the effect of a small change to the blue
weight will double too. Hence, to compute the derivatives of the weights, we need
to calculate and store the activations at the hidden layers. This is known as the
forward pass since it involves running the network equations sequentially.

<img src="assets/Chap07/Train2BPIntuitions2.svg" style="filter: invert(1);" width="100%">

Backpropagation backward pass. a) To compute how a change to
a weight feeding into layer h3 (blue arrow) changes the loss, we need to know
how the hidden unit in h3 changes the model output f and how f changes the
loss (orange arrows). b) To compute how a small change to a weight feeding
into h2 (blue arrow) changes the loss, we need to know (i) how the hidden unit
in h2 changes h3, (ii) how h3 changes f , and (iii) how f changes the loss (orange
arrows). c) Similarly, to compute how a small change to a weight feeding into h1
(blue arrow) changes the loss, we need to know how h1 changes h2 and how
these changes propagate through to the loss (orange arrows). The backward pass
first computes derivatives at the end of the network and then works backward to
exploit the inherent redundancy of these computations.

## Toy example


\begin{eqnarray}
  \mbox{f}[x,\boldsymbol\phi] = \beta_3+\omega_3\cdot\cos\Bigl[\beta_2+\omega_2\cdot\exp\bigl[\beta_1+\omega_1\cdot\sin[\beta_0+\omega_0\cdot x]\bigr]\Bigr],
 \end{eqnarray}

\begin{eqnarray}
 \ell_i = (\mbox{f}[x_i,\boldsymbol\phi]-y_i)^2,
 \end{eqnarray}

\begin{eqnarray}
 \frac{\partial \ell_i}{\partial \beta_{0}}, \quad \frac{\partial \ell_i}{\partial \omega_0}, \quad \frac{\partial \ell_i}{\partial \beta_{1}}, \quad \frac{\partial \ell_i}{\partial \omega_1}, \quad
 \frac{\partial \ell_i}{\partial \beta_{2}}, \quad \frac{\partial \ell_i}{\partial \omega_{2}}, \quad \frac{\partial \ell_i}{\partial \beta_{3}}, \quad\mbox{and} \quad \frac{\partial \ell_i}{\partial \omega_{3}}.
 \end{eqnarray}

\begin{eqnarray}\label{eq:train2_complicated_deriv}
 \frac{\partial \ell_i}{\partial \omega_{0}} &=& -2 \left( \beta_3+\omega_3\cdot\cos\Bigl[\beta_2+\omega_2\cdot\exp\bigl[\beta_1+\omega_1\cdot\sin[\beta_0+\omega_0\cdot x_i]\bigr]\Bigr]-y_i\right)\nonumber \\
 &&\hspace{0.5cm}\cdot \omega_1\omega_2\omega_3\cdot x_i\cdot\cos[\beta_0+\omega_0 \cdot x_i]\cdot\exp\Bigl[\beta_1 + \omega_1 \cdot \sin[\beta_0+\omega_0\cdot x_i]\Bigr]\nonumber\\
 && \hspace{1cm}\cdot \sin\biggl[\beta_2+\omega_2\cdot \exp\Bigl[\beta_1 + \omega_1 \cdot \sin[\beta_0+\omega_0\cdot x_i]\Bigr]\biggr].
 \end{eqnarray}


<img src="assets/Chap07/Train2BP1.svg" style="filter: invert(1);" width="100%">

Backpropagation forward pass. We compute and store each of the
intermediate variables in turn until we finally calculate the loss.

\begin{eqnarray}
 f_{0} &=& \beta_{0} + \omega_{0}\cdot x_i\nonumber\\
 h_{1} &=& \sin[f_{0}]\nonumber\\
 f_{1} &=& \beta_{1} + \omega_{1}\cdot h_{1}\nonumber\\
 h_{2} &=& \exp[f_{1}]\nonumber\\
 f_{2} &=& \beta_{2} + \omega_{2} \cdot h_{2}\nonumber\\
 h_{3} &=& \cos[f_{2}]\nonumber\\
 f_{3} &=& \beta_{3} + \omega_{3}\cdot h_{3}\nonumber\\
 \ell_{i} &=& (f_{3}-y_{i})^2.
 \end{eqnarray}

\begin{eqnarray}
 \frac{\partial \ell_i}{\partial f_{3}}, \quad \frac{\partial \ell_i}{\partial h_3}, \quad \frac{\partial \ell_i}{\partial f_2}, \quad
 \frac{\partial \ell_i}{\partial h_2}, \quad \frac{\partial \ell_i}{\partial f_1}, \quad \frac{\partial \ell_i}{\partial h_1}, \quad\mbox{and} \quad \frac{\partial \ell_i}{\partial f_0}.
 \end{eqnarray}

\begin{eqnarray}
 \frac{\partial \ell_i}{\partial f_{3}} = 2(f_3-y_i).
 \end{eqnarray}

\begin{eqnarray}
 \frac{\partial \ell_i}{\partial h_{3}} =\frac{\partial f_{3}}{\partial h_{3}} \frac{\partial \ell_i}{\partial f_{3}} .
 \end{eqnarray}


<img src="assets/Chap07/Train2BP2.svg" style="filter: invert(1);" width="100%">

Backpropagation backward pass #1. We work backward from the end
of the function computing the derivatives ∂ℓi/∂fk and ∂ℓi/∂hk of the loss with
respect to the intermediate quantities. Each derivative is computed from the
previous one by multiplying by terms of the form ∂fk/∂hk or ∂hk/∂fk−1.


\begin{eqnarray}
 \frac{\partial \ell_i}{\partial f_{2}} &=& \frac{\partial h_{3}}{\partial f_{2}}\left(
 \frac{\partial f_{3}}{\partial h_{3}}\frac{\partial \ell_i}{\partial f_{3}} \right)
 \nonumber \\
 \frac{\partial \ell_i}{\partial h_{2}} &=& \frac{\partial f_{2}}{\partial h_{2}}\left(\frac{\partial h_{3}}{\partial f_{2}}\frac{\partial f_{3}}{\partial h_{3}}\frac{\partial \ell_i}{\partial f_{3}}\right)\nonumber \\
 \frac{\partial \ell_i}{\partial f_{1}} &=& \frac{\partial h_{2}}{\partial f_{1}}\left( \frac{\partial f_{2}}{\partial h_{2}}\frac{\partial h_{3}}{\partial f_{2}}\frac{\partial f_{3}}{\partial h_{3}}\frac{\partial \ell_i}{\partial f_{3}} \right)\nonumber \\
 \frac{\partial \ell_i}{\partial h_{1}} &=& \frac{\partial f_{1}}{\partial h_{1}}\left(\frac{\partial h_{2}}{\partial f_{1}} \frac{\partial f_{2}}{\partial h_{2}}\frac{\partial h_{3}}{\partial f_{2}}\frac{\partial f_{3}}{\partial h_{3}}\frac{\partial \ell_i}{\partial f_{3}} \right)\nonumber \\
 \frac{\partial \ell_i}{\partial f_{0}} &=& \frac{\partial h_{1}}{\partial f_{0}}\left(\frac{\partial f_{1}}{\partial h_{1}}\frac{\partial h_{2}}{\partial f_{1}} \frac{\partial f_{2}}{\partial h_{2}}\frac{\partial h_{3}}{\partial f_{2}}\frac{\partial f_{3}}{\partial h_{3}}\frac{\partial \ell_i}{\partial f_{3}} \right).\label{eq:train2_simple_chain}
 \end{eqnarray}

\begin{eqnarray}
 \frac{\partial \ell_i}{\partial \beta_{k}} &=& \frac{\partial f_{k}}{\partial \beta_{k}}\frac{\partial \ell_i}{\partial f_{k}}\nonumber \\
 \frac{\partial \ell_i}{\partial \omega_{k}} &=& \frac{\partial f_{k}}{\partial \omega_{k}}\frac{\partial \ell_i}{\partial f_{k}}.
 \end{eqnarray}

\begin{eqnarray}
 \frac{\partial f_{k}}{\partial \beta_{k}} = 1 \quad\quad\mbox{and}\quad \quad \frac{\partial f_{k}}{\partial \omega_{k}} &=& h_{k}.
 \end{eqnarray}

<img src="assets/Chap07/Train2BP3.svg" style="filter: invert(1);" width="100%">

Backpropagation backward pass #2. Finally, we compute the derivatives
∂ℓi/∂βk and ∂ℓi/∂ωk. Each derivative is computed by multiplying the
term ∂ℓi/∂fk by ∂fk/∂βk or ∂fk/∂ωk as appropriate.

\begin{eqnarray}
 \frac{\partial f_{0}}{\partial \beta_{0}} = 1 \quad\quad\mbox{and}\quad \quad \frac{\partial f_{0}}{\partial \omega_{0}} &=& x_{i}.
 \end{eqnarray}

