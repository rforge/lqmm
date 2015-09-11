\name{predict.lqmm}
\alias{predint}
\alias{predint.lqmm}
\alias{predict.lqmm}

\title{
Predictions from an \code{lqmm} Object
}

\description{
The predictions at level 0 correspond to population predictions (based only on the fixed effects estimates). The predictions at level 1 are obtained by adding the best linear predictions of the random effects to the predictions at level 0. The function \code{predint} will produce 1-alpha confidence intervals based on bootstrap centiles.
}

\usage{
\method{predict}{lqmm}(object, level = 0, ...)
\method{predint}{lqmm}(object, level = 0, alpha = 0.05, R = 50,
	seed = round(runif(1, 1, 10000)))
}

\arguments{
  \item{object}{
an \code{lqmm} object.
}
  \item{level}{
an optional integer vector giving the level of grouping to be used in obtaining the predictions. Level zero corresponds to the population predictions.
}
  \item{alpha}{
1-\code{alpha} is the confidence level.  
}
  \item{R}{
number of bootstrap replications.
  }
  \item{seed}{
optional random number generator seed.
  }
  \item{\dots}{
not used.
}
}

\value{
a vector or a matrix of predictions for \code{predict.lqmm}. A data frame or a list of data frames for \code{predint.lqmm} containing predictions, lower and upper bounds of prediction intervals, and standard errors.
}

\references{
Geraci M and Bottai M (2014). Linear quantile mixed models. Statistics and Computing, 24(3), 461--479. doi: 10.1007/s11222-013-9381-9.
}

\author{
Marco Geraci
}


\seealso{
\code{\link{lqmm}}, \code{\link{ranef.lqmm}}, \code{\link{coef.lqmm}}
}

\keyword{prediction}
