---
title: Linear Regression

---

::: {.callout-tip}
## Slides
[Slides](https://docs.google.com/presentation/d/19xKdVzZoa0kbkkm8uI9Hp_NWHs4Nfw8Pg-5ONJf0c0Y/edit?slide=id.p#slide=id.p)
::: 

## Supervised Learning overview 

\begin{eqnarray}
  \mathbf{y} = \mbox{\bf f}[\mathbf{x}].
 \end{eqnarray}

\begin{eqnarray}
  \mathbf{y} = \mbox{\bf f}[\mathbf{x}, \boldsymbol\phi].
\end{eqnarray}

\begin{eqnarray}
  \hat{\boldsymbol\phi} = \mathop{\rm argmin}_{\boldsymbol\phi}\Bigl[L\left[\boldsymbol\phi\right] \Bigr].
\end{eqnarray}

## Linear regression example 

### 1D linear regression model


\begin{eqnarray}\label{eq:sl_linear_regression}
  y &=& \mbox{f}[x,\boldsymbol\phi]\nonumber \\
  &=&\phi_{0}+\phi_{1}x.
\end{eqnarray}


### Loss


\begin{eqnarray}\label{eq:sl_loss_function}
  L[\boldsymbol\phi] &=& \sum_{i=1}^{I} \left(\mbox{f}[x_{i}, \boldsymbol\phi]-y_{i}\right)^{2}\nonumber \\
  &=& \sum_{i=1}^{I} \left(\phi_{0}+\phi_{1}x_i-y_{i}\right)^{2}.\\
  
 \end{eqnarray}


\begin{eqnarray}
  \hat{\boldsymbol\phi} &=& \mathop{\rm argmin}_{\boldsymbol\phi}\Bigl[L[\boldsymbol\phi]\Bigr]\nonumber \\
  &=& \mathop{\rm argmin}_{\boldsymbol\phi}\left[\sum_{i=1}^{I} \left(\mbox{f}[x_{i}, \boldsymbol\phi]-y_{i}\right)^{2}\right]\nonumber \\
  &=& \mathop{\rm argmin}_{\boldsymbol\phi}\left[\sum_{i=1}^{I} \left(\phi_{0}+\phi_{1}x_i-y_{i}\right)^{2}\right].
 \end{eqnarray}

<img src="assets/Chap02/SupervisedLinear.svg" style="filter: invert(1);">

Linear regression model. For a given choice of parameters ϕ= [ϕ0,ϕ1], the model makes a prediction for the out-
put (y-axis) based on the input (x-axis).

Different choices for the y-intercept ϕ0 and the slope ϕ1 change these predictions (cyan, orange, and gray lines). The linear regression model (equation 2.4) defines a family of input/output relations (lines) and the parameters determine the member of the family (the particular line). (Interactive figure)

<img src="assets/Chap02/SupervisedLinearFitError.svg" style="filter: invert(1);" width="100%">

Linear regression training data, model, and loss. a) The training data (orange points) consist of I = 12 input/output pairs {xi,yi}. b–d) Each panel shows the linear regression model with different parameters. Depending on the choice of y-intercept and slope parameters ϕ= [ϕ0,ϕ1], the model errors (orange dashed lines) may be larger or smaller. The loss L is the sum of the squares of these errors. The parameters that define the lines in panels (b) and (c) have large losses L= 7.07 and L= 10.28, respectively because the models fit badly.
The loss L= 0.20 in panel (d) is smaller because the model fits well; in fact, this has the smallest loss of all possible lines, so these are the optimal parameters.
(Interactive figure)

<img src="assets/Chap02/SupervisedSurface.svg" style="filter: invert(1);" width="100%">

Loss function for linear regression model with the dataset in figure 2.2a.
a) Each combination of parameters ϕ= [ϕ0,ϕ1] has an associated loss. The resulting loss function L[ϕ] can be visualized as a surface. The three circles represent
the lines from figure 2.2b–d. b) The loss can also be visualized as a heatmap, where brighter regions represent larger losses; here we are looking straight down
at the surface in (a) from above and gray ellipses represent isocontours. The best fitting line (figure 2.2d) has the parameters with the smallest loss (green circle).


<img src="assets/Chap02/SupervisedOpt.svg" style="filter: invert(1);" width="100%">

Linear regression training. The goal is to find the y-intercept and slope parameters that correspond to the smallest loss. a) Iterative training algorithms
initialize the parameters randomly and then improve them by “walking downhill” until no further improvement can be made. Here, we start at position 0 and move
a certain distance downhill (perpendicular to the contours) to position 1. Then we re-calculate the downhill direction and move to position 2. Eventually, we
reach the minimum of the function (position 4). b) Each position 0–4 from panel (a) corresponds to a different y-intercept and slope and so represents a different
line. As the loss decreases, the lines fit the data more closely. (Interactive figure)

### Training

### Testing