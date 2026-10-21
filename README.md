# A roadmap for formalizing CFTs

This is a repository to formalize the structures appearing in reflection positive conformal field theories (CFTs) in $d > 2$ dimensions.

The plan (see [PLAN.md](PLAN.md)) is to first build all the necessary tools to analyze *four-point functions of identical scalar primary operators*. We will assume a conformal block decomposition and use it to prove results like Tauberian theorems for the asymptotics and light-cone bootstrap theorems. This approach will allow us to jump directly to mathematical physics questions of present-day interest.

In the longer run the idea is to introduce more fundamental axioms from which all these results will ultimately follow. This needs to be done carefully, and it will be beneficial to have concrete theorems to aim for.

Roughly speaking the idea will be to introduce as axioms conformal covariance and a Hilbert space in radial quantization. Postulating further the existence of a resolution of the identity will allow us to derive the state-operator correspondence, and thereby a convergent series expansion for $n$-point correlation functions of arbitrary local operators. 

Natural extensions will include the generalization to curved spaces and non-local operators like defects and interfaces.

We will always start the derivations in Euclidean signature. In the long run it might be possible to prove that the CFT axioms we postulate are fulfilled by a properly constructed QFT, for example the continuum limit of a lattice theory, and this will be most naturally done in Euclidean signature.

Our axioms will therefore mimic the OS axioms, although we have much more control in CFTs than in general QFTs. Lorentzian CFTs, and the associated Wightman functions, will be defined by analytic continuation.

While AI is used heavily throughout this repository, we aim for the documentation at https://baltvanrees.github.io/cft/docs/CFT.html to be maximally useful and educational. Currently all the files in the `CFT` folder have been human-verified, but those in sub-folders have not.
