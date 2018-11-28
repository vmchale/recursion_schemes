# recursion_schemes

[![Build Status](https://travis-ci.org/vmchale/recursion_schemes.svg?branch=master)](https://travis-ci.org/vmchale/recursion\_schemes)

This is a library providing recursion schemes for Idris. It it is loosely based
on Edward Kmett's [Haskell
library](https://hackage.haskell.org/package/recursion-schemes).

## Installation

First, install [idris-free](https://github.com/idris-hackers/idris-free),
[comonad](https://github.com/vmchale/comonad) and [composition](https://github.com/vmchale/composition). Then:

```
idris --install recursion_schemes.ipkg
```

To run the tests, install [specdris](https://github.com/pheymann/specdris).
Then:

```
idris --testpkg test.ipkg
```

### elba

If you use [elba](https://github.com/elba/elba) to manage your Idris packages,
adding this package as a dependency is as easy as:

```toml
# elba.toml
[dependencies]
"vmchale/recursion_schemes" = { git = "https://github.com/vmchale/recursion_schemes" }
```

To run the tests, clone the repository and run `elba test` in it.

## Use

The classic paper [Functional programming with bananas, lenses, envelopes and
barbed wire](https://link.springer.com/chapter/10.1007/3540543961_7) is the
inspiration behind the Haskell library and is the standard reference on the
topic. You may also find [Law and Order in
Algorithmics](https://pdfs.semanticscholar.org/7ca8/326eb63f32502c0fc2324b6217a7bc7e8af4.pdf)
to be of use.

### Examples

In the `Test.Spec` module there are several examples, including a catamorphism,
a zygomorphism, a mutumorphism, an Elgot algebra, a paramorphism, a
dynamorphism, and a hylomorphism.

### Documentation

You can find documentation
[here](https://vmchale.github.io/recursion_schemes/index.html).
