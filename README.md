# recursion_schemes

This is a library providing recursion schemes for Idris. It it is loosely based
on Edward Kmett's [Haskell
library](https://hackage.haskell.org/package/recursion-schemes).

As it stands, it segfaults if you try to do anything. So it is very much a work
in progress.

## Installation

To install:

```
idris --install recursion_schemes.ipkg
```

To run the tests, install [specdris](https://github.com/pheymann/specdris).
Then:

```
idris --testpkg recursion_schemes_test.ipkg
```

## Use

The classic paper [Functional programming with bananas, lenses, envelopes and
barbed wire](https://link.springer.com/chapter/10.1007/3540543961_7) is the
inspiration behind the Haskell library and is the standard reference on the
topic. You may also find [Law and Order in
Algorithmics](https://pdfs.semanticscholar.org/7ca8/326eb63f32502c0fc2324b6217a7bc7e8af4.pdf)
to be of use.

### Examples

In the `Test.Spec` module there are several examples.
