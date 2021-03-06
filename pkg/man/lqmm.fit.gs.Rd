\name{lqmm.fit.gs}
\alias{lqmm.fit.gs}

\title{
Linear Quantile Mixed Models Fitting by Gradient Search
}
\description{
This function controls the arguments to be passed to routines written in C for LQMM estimation. The optimization algorithm is based on the gradient of the Laplace log--likelihood (Bottai, Orsini and Geraci, 2014; Geraci and Bottai, 2014).
}
\usage{
lqmm.fit.gs(theta_0, x, y, z, weights, cov_name, V, W, sigma_0, tau,
	group, control)
}

\arguments{
  \item{theta_0}{
starting values for the linear predictor.
}
  \item{x}{
the model matrix for fixed effects (see details).
}
  \item{y}{
the model response (see details).
}
  \item{z}{
the model matrix for random effects (see details).
}
  \item{weights}{
the weights used in the fitting process (see details).
}

  \item{cov_name}{
variance--covariance matrix of the random effects. Default is \code{pdIdent}. See details.
}

  \item{V}{
nodes of the quadrature.
}
  \item{W}{
weights of the quadrature.
}
  \item{sigma_0}{
starting value for the scale parameter.
  }
  \item{tau}{
the quantile(s) to be estimated.
}
  \item{group}{
the grouping factor (see details).
}
  \item{control}{
list of control parameters used for optimization (see \code{\link{lqmmControl}}).
}
}
\details{
In \code{\link{lqmm}}, see argument \code{fit} for generating a list of arguments to be called by this function; see argument \code{covariance} for alternative variance--covariance matrices.

NOTE: the data should be ordered by \code{group} when passed to \code{lqmm.fit.gs} (such ordering is performed by \code{\link{lqmm}}). 
}

\value{
An object of class "list" containing the following components:

\item{theta}{a vector of coefficients, including the "raw" variance--covariance parameters (see \code{\link{VarCorr.lqmm}}).}
\item{scale}{the scale parameter.}
\item{gradient}{the gradient.}
\item{logLik}{the log--likelihood.}
\item{opt}{number of iterations when the estimation algorithm stopped for lower (theta) and upper (scale) loop.}.
}

\references{
Bottai M, Orsini N, Geraci M. (2014). A gradient search maximization algorithm for the asymmetric Laplace likelihood, Journal of Statistical Computation and Simulation (in press).

Geraci M and Bottai M (2014). Linear quantile mixed models. Statistics and Computing, 24(3), 461--479.
}
\author{
Marco Geraci}


\seealso{
\code{\link{lqmm}}
}

\examples{
set.seed(123)

M <- 50
n <- 10
test <- data.frame(x = runif(n*M,0,1), group = rep(1:M,each=n))
test$y <- 10*test$x + rep(rnorm(M, 0, 2), each = n) + rchisq(n*M, 3)
lqmm.ls <- lqmm(fixed = y ~ x, random = ~ 1, group = group,
	data = test, fit = FALSE)

do.call("lqmm.fit.gs", lqmm.ls)

}

\keyword{fitting}
