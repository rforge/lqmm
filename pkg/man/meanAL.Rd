\name{meanAL}
\alias{varAL}
\alias{invvarAL}
\alias{meanAL}

\title{
Functions for Asymmetric Laplace Distribution Parameters
}

\description{
Accessory functions.
}

\usage{
meanAL(mu, sigma, iota)
varAL(sigma, iota)
invvarAL(x, iota)
}

\arguments{
  \item{mu}{
location parameter.
}
  \item{sigma}{
scale parameter.
}
  \item{iota}{
skewness parameter.
}
  \item{x}{
numeric value.
}


}
\details{
\code{meanAL} computes the mean of an asymmetric Laplace with parameters \code{mu}, \code{sigma} and \code{iota}.

\code{varAL} computes the variance of an asymmetric Laplace with parameters \code{sigma} and \code{iota}.

\code{invvarAL} computes the scale parameter of an asymmetric Laplace with parameter \code{iota} and variance \code{x}.
}


\references{
Yu K and Zhang J (2005). A three-parameter asymmetric Laplace distribution and its extension. Communications in Statistics-Theory and Methods 34, 1867--1879.
}

\author{
Marco Geraci
}


\seealso{
\code{\link{dal}}, \code{\link{mleAL}}
}

\keyword{asymmetric Laplace distribution}
\keyword{maximum likelihood estimation}

