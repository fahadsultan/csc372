---
title: Deep Neural Networks

---

::: {.callout-tip}
## Slides
[Slides](https://docs.google.com/presentation/d/1Bk61VR7h6q_lAa02fRCy464I2wyXLJg8nJQ1qKdyFLA/edit?slide=id.g32ea142b459_0_0#slide=id.g32ea142b459_0_0)
::: 

## Composing neural networks 

\begin{eqnarray}\label{eq:dnn_comp_in}
 h_{1} &=& \mbox{a}[\theta_{10} + \theta_{11}x] \nonumber \\
 h_{2} &=& \mbox{a}[\theta_{20} + \theta_{21}x] \nonumber \\
 h_{3} &=& \mbox{a}[\theta_{30} + \theta_{31}x],
 \end{eqnarray}

\begin{eqnarray}\label{eq:dnn_comp}
 y = \phi_{0}+\phi_{1}h_{1}+\phi_{2}h_{2}+\phi_{3}h_{3}.
 \end{eqnarray}


<img src="assets/Chap04/DeepConcat.svg" style="filter: invert(1);" width="100%">

Composing two single-layer networks with three hidden units each. a)
The output y of the first network constitutes the input to the second network. b)
The first network maps inputs x ∈ [−1, 1] to outputs y ∈ [−1, 1] using a function
comprising three linear regions that are chosen so that they alternate the sign
of their slope (fourth linear region is outside range of graph). Multiple inputs x
(gray circles) now map to the same output y (cyan circle). c) The second network
defines a function comprising three linear regions that takes y and returns y
′ (i.e.,
the cyan circle is mapped to the brown circle). d) The combined effect of these
two functions when composed is that (i) three different inputs x are mapped to
any given value of y by the first network and (ii) are processed in the same way by
the second network; the result is that the function defined by the second network
in panel (c) is duplicated three times, variously flipped and rescaled according to
the slope of the regions of panel (b). (Interactive figure)


\begin{eqnarray}\label{eq:dnn_comp_2}
 h'_{1} &=& \mbox{a}[\theta'_{10} + \theta'_{11}y] \nonumber \\
 h'_{2} &=& \mbox{a}[\theta'_{20} + \theta'_{21}y] \nonumber \\
 h'_{3} &=& \mbox{a}[\theta'_{30} + \theta'_{31}y],
 \end{eqnarray}

\begin{eqnarray} \label{eq:dnn_comp_out}
 y' = \phi'_{0}+\phi'_{1}h'_{1}+\phi'_{2}h'_{2}+\phi'_{3}h'_{3}.
 \end{eqnarray}

## From composing networks to deep networks

\begin{eqnarray}\label{eq:dnn_deep_linear}
 h'_{1} &=\quad \mbox{a}[\theta'_{10} + \theta'_{11}y] &=\quad \mbox{a}[\theta'_{10} + \theta'_{11}\phi_{0}+\theta'_{11}\phi_{1}h_{1}+\theta'_{11}\phi_{2}h_{2}+\theta'_{11}\phi_{3}h_{3}] \nonumber \\
 h'_{2} &= \quad\mbox{a}[\theta'_{20} + \theta'_{21}y] &=\quad \mbox{a}[\theta'_{20} + \theta'_{21}\phi_{0}+\theta'_{21}\phi_{1}h_{1}+\theta'_{21}\phi_{2}h_{2}+\theta'_{21}\phi_{3}h_{3}] \nonumber \\
 h'_{3} &=\quad \mbox{a}[\theta'_{30} + \theta'_{31}y] &=\quad \mbox{a}[\theta'_{30} + \theta'_{31}\phi_{0}+\theta'_{31}\phi_{1}h_{1}+\theta'_{31}\phi_{2}h_{2}+\theta'_{31}\phi_{3}h_{3}],
 \end{eqnarray}

\begin{eqnarray}\label{eq:dnn_three_layer_middle}
 h'_{1} &=& \mbox{a}[\psi_{10} + \psi_{11}h_{1}+ \psi_{12}h_{2}+ \psi_{13}h_{3}] \nonumber \\
 h'_{2} &=& \mbox{a}[\psi_{20} + \psi_{21}h_{1}+ \psi_{22}h_{2}+ \psi_{23}h_{3}] \nonumber \\
 h'_{3} &=& \mbox{a}[\psi_{30} + \psi_{31}h_{1}+ \psi_{32}h_{2}+ \psi_{33}h_{3}],
 \end{eqnarray}

<img src="assets/Chap04/DeepTwoLayer2D.svg" style="filter: invert(1);" width="100%">


Composing neural networks with a 2D input. a) The first network
(from figure 3.8) has three hidden units and takes two inputs x1 and x2 and returns
a scalar output y. This is passed into a second network with two hidden units to
produce y
′. b) The first network produces a function consisting of seven linear
regions, one of which is flat. c) The second network defines a function comprising
two linear regions in y ∈ [−1, 1]. d) When these networks are composed, each of
the six non-flat regions from the first network is divided into two new regions by
the second network to create a total of 13 linear regions.

<img src="assets/Chap04/DeepFold.svg" style="filter: invert(1);" width="100%">

Deep networks as folding input space. a) One way to think about
the first network from figure 4.1 is that it “folds” the input space back on top
of itself. b) The second network applies its function to the folded space. c) The
final output is revealed by “unfolding” again.

<img src="assets/Chap04/DeepTwoLayer.svg" style="filter: invert(1);" width="100%">

Neural network with one input, one output, and two hidden layers, each containing three hidden units.

## Deep Neural Networks


\begin{eqnarray}\label{eq:dnn_three_layer_in}
 h_{1} &=& \mbox{a}[\theta_{10} + \theta_{11}x] \nonumber \\
 h_{2} &=& \mbox{a}[\theta_{20} + \theta_{21}x] \nonumber \\
 h_{3} &=& \mbox{a}[\theta_{30} + \theta_{31}x],
 \end{eqnarray}

\begin{eqnarray}\label{eq:dnn_three_layer_middle2}
 h'_{1} &=& \mbox{a}[\psi_{10} + \psi_{11}h_{1}+ \psi_{12}h_{2}+ \psi_{13}h_{3}] \nonumber \\
 h'_{2} &=& \mbox{a}[\psi_{20} + \psi_{21}h_{1}+ \psi_{22}h_{2}+ \psi_{23}h_{3}] \nonumber \\
 h'_{3} &=& \mbox{a}[\psi_{30} + \psi_{31}h_{1}+ \psi_{32}h_{2}+ \psi_{33}h_{3}],
 \end{eqnarray}

\begin{eqnarray}\label{eq:dnn_three_layer_out}
 y' = \phi'_{0}+\phi'_{1}h'_{1}+\phi'_{2}h'_{2}+\phi'_{3}h'_{3}.
 \end{eqnarray}


\begin{eqnarray}\label{eq:dnn_expanded}
 y' &=& \phi'_{0}+\phi'_{1}\mbox{a}\left[\psi_{10} + \psi_{11}\mbox{a}[\theta_{10} + \theta_{11}x] + \psi_{12}\mbox{a}[\theta_{20} + \theta_{21}x]+ \psi_{13}\mbox{a}[\theta_{30} + \theta_{31}x]\right]\nonumber \\
 &&\hspace{0.55cm}+\phi'_{2}\mbox{a}[\psi_{20} + \psi_{21}\mbox{a}[\theta_{10} + \theta_{11}x] + \psi_{22}\mbox{a}[\theta_{20} + \theta_{21}x]+ \psi_{23}\mbox{a}[\theta_{30} + \theta_{31}x]] \nonumber\\
 &&\hspace{0.55cm}+\phi'_{3}\mbox{a}[\psi_{30} + \psi_{31}\mbox{a}[\theta_{10} + \theta_{11}x] + \psi_{32}\mbox{a}[\theta_{20} + \theta_{21}x]+ \psi_{33}\mbox{a}[\theta_{30} + \theta_{31}x]],\nonumber \\
 \end{eqnarray}

### Hyperparameters

<img src="assets/Chap04/DeepBuildUp.svg" style="filter: invert(1);" width="100%">

Computation for the deep network in figure 4.4. a–c) The inputs
to the second hidden layer (i.e., the pre-activations) are three piecewise linear
functions where the “joints” between the linear regions are at the same places
(see figure 3.6). d–f) Each piecewise linear function is clipped to zero by the
ReLU activation function. g–i) These clipped functions are then weighted with
parameters ϕ
′
1, ϕ
′
2, and ϕ
′
3, respectively. j) Finally, the clipped and weighted
functions are summed and an offset ϕ
′
0 that controls the overall height is added.
(Interactive figure)


<img src="assets/Chap04/DeepKLayer.svg" style="filter: invert(1);" width="100%">

Matrix notation for network with Di = 3-dimensional input x, Do = 2-
dimensional output y, and K = 3 hidden layers h1, h2, and h3 of dimensions
D1 = 4, D2 = 2, and D3 = 3 respectively. The weights are stored in matrices Ωk
that multiply the activations from the preceding layer to create the pre-activations
at the subsequent layer. For example, the weight matrix Ω1 that computes the
pre-activations at h2 from the activations at h1 has dimension 2×4. It is applied
to the four hidden units in layer one and creates the inputs to the two hidden
units at layer two. The biases are stored in vectors βk and have the dimension
of the layer into which they feed. For example, the bias vector β2 is length three
because layer h3 contains three hidden units.

### Matrix Notation 


\begin{eqnarray}
  \begin{bmatrix}
  h_{1} \\ h_{2} \\ h_{3}
  \end{bmatrix}
  = \mbox{\bf a}\left[\begin{bmatrix}\theta_{10}\\ \theta_{20}\\ \theta_{30} \end{bmatrix}+\begin{bmatrix}\theta_{11}\\\theta_{21}\\\theta_{31}\end{bmatrix}x\right],
 \end{eqnarray}

\begin{eqnarray}
  \begin{bmatrix}
  h'_{1} \\ h'_{2} \\h'_{3} 
  \end{bmatrix}
  =\mbox{\bf a}\left[\begin{bmatrix}\psi_{10} \\ \psi_{20}\\ \psi_{30}\end{bmatrix} + \begin{bmatrix}\psi_{11} &\psi_{12} & \psi_{13} \\\psi_{21} &\psi_{22} & \psi_{23} \\\psi_{31} &\psi_{32} & \psi_{33} \end{bmatrix} \begin{bmatrix}
  h_{1} \\ h_{2} \\ h_{3}
  \end{bmatrix} \right],
  \end{eqnarray}

\begin{eqnarray}
  y' = \phi'_{0} + \begin{bmatrix} \phi'_{1} & \phi'_{2} & \phi'_{3} \end{bmatrix}\begin{bmatrix}h'_{1} \\ h'_{2} \\h'_{3} \end{bmatrix},
 \end{eqnarray}


\begin{eqnarray}
  \mathbf{h} &=& \mbox{\bf a}\left[\boldsymbol\theta_{0}+\boldsymbol\theta x\right] \nonumber\\
  \mathbf{h}' &=& \mbox{\bf a}\left[\boldsymbol\psi_{0}+\boldsymbol\Psi \mathbf{h}\right] \nonumber \\
  y' &=& \phi'_{0} + \boldsymbol\phi' \mathbf{h}',
 \end{eqnarray}

### General formulation

\begin{eqnarray}\label{eq:dnn_la1}
  \mathbf{h}_{1} &=& \mathbf{a}[\boldsymbol\beta_{0} +\boldsymbol\Omega_{0}\mathbf{x}]\nonumber \\
  \mathbf{h}_{2} &=& \mathbf{a}[\boldsymbol\beta_{1} +\boldsymbol\Omega_{1}\mathbf{h}_{1}]\nonumber \\
  \mathbf{h}_{3} &=& \mathbf{a}[\boldsymbol\beta_{2} +\boldsymbol\Omega_{2}\mathbf{h}_{2}]\nonumber \\
  &\vdots&\nonumber\\
  \mathbf{h}_{K} &=& \mathbf{a}[\boldsymbol\beta_{K-1} +\boldsymbol\Omega_{K-1}\mathbf{h}_{K-1}] \nonumber\\
  \mathbf{y} &=& \boldsymbol\beta_{K} +\boldsymbol\Omega_{K}\mathbf{h}_{K}.
 \end{eqnarray}

## Shallow vs. deep neural networks

### Ability to approximate different functions 

### Number of linear regresions per parameter 

### Depth efficiency

### Large, structured inputs 

<img src="assets/Chap04/DeepParams.svg" style="filter: invert(1);" width="100%">

The maximum number of linear regions for neural networks increases
rapidly with the network depth. a) Network with Di = 1 input. Each curve represents
a fixed number of hidden layers K, as we vary the number of hidden units
D per layer. For a fixed parameter budget (horizontal position), deeper networks
produce more linear regions than shallower ones. A network with K = 5 layers
and D = 10 hidden units per layer has 471 parameters (highlighted point) and
can produce 161,051 regions. b) Network with Di = 10 inputs. Each subsequent
point along a curve represents ten hidden units. Here, a model with K = 5 layers
and D = 50 hidden units per layer has 10,801 parameters (highlighted point) and
can create more than 1040 linear regions.

### Training and generalization 

<img src="assets/Chap04/DeepConcatQuestion.svg" style="filter: invert(1);" width="100%">

Composition of two networks for problem 4.1. a) The output y of the
first network becomes the input to the second. b) The first network computes
this function with output values y ∈ [−1, 1]. c) The second network computes
this function on the input range y ∈ [−1, 1].

<img src="assets/Chap04/DeepProbZeroCross.svg" style="filter: invert(1);" width="100%">

Hidden unit activations for problem 4.8. a) First hidden unit has a
joint at position x = 1/6 and a slope of one in the active region. b) Second hidden
unit has a joint at position x = 2/6 and a slope of one in the active region. c)
Third hidden unit has a joint at position x = 4/6 and a slope of minus one in the
active region.






\begin{eqnarray}\label{eq:dnn_la2}
  \mathbf{y}\!\! &\!\!=\!\!& \!\!\boldsymbol\beta_{K} +\boldsymbol\Omega_{K}\mathbf{a}\left[\boldsymbol\beta_{K-1} +\boldsymbol\Omega_{K-1}\mathbf{a}\left[\ldots
  \boldsymbol\beta_{2} +\boldsymbol\Omega_{2}\mathbf{a}\left[\boldsymbol\beta_{1} +\boldsymbol\Omega_{1}\mathbf{a}\left[\boldsymbol\beta_{0} +\boldsymbol\Omega_{0}\mathbf{x}\right]\right]\ldots\right]\right].\nonumber \\
 \end{eqnarray}

\begin{eqnarray}\label{eq:dnn_deep_param_calc}
  N_{r} = \left(\frac{D}{D_{i}}+1\right)^{D_{i}(K-1)}\cdot\sum_{j=0}^{D_{i}}\binom{D}{j}.
 \end{eqnarray}


\begin{eqnarray}
 \mbox{ReLU}\Bigl[\boldsymbol\beta_{1}\!+\!\lambda_1\!\cdot\!\boldsymbol\Omega_{1}\mbox{ReLU}\left[\boldsymbol\beta_{0}\!+\!\lambda_{0}\cdot\boldsymbol\Omega_{0}\mathbf{x}\right] \Bigr]\!=\! \lambda_0\lambda_{1}\cdot \mbox{ReLU}\left[\frac{1}{\lambda_0\lambda_1}\boldsymbol\beta_{1}\!+\!\boldsymbol\Omega_{1}\mbox{ReLU}\left[\frac{1}{\lambda_0}\boldsymbol\beta_{0}\!+\!\boldsymbol\Omega_{0}\mathbf{x}\right]\right],
 \end{eqnarray}

