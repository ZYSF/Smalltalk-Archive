# Smalltalk-Archive

An archival fork of Public Domain Smalltalk (PDST), slightly updated and optionally integrated with [HAL/L2](http://zakfenton.com/projects/hal) (sold separately).

## Original Code

Public Domain Smalltalk wasn't originally developed by me. It's mostly the work of Douglas E. Hammond and Timothy Budd. Of course, the most credit goes to Alan Kay, the original developer of the Smalltalk language and teacher of Object-Oriented Programming.

### Disclaimer

You understand and agree that this material is entirely in the public
domain, that it is made available to you without charge and that it will
only be used based on the express disclaimer by Douglas E. Hammond and
all other persons or organizations participating in its production,
storage and transmission of any warranty or guarantee, express or
implied, of any aspect of this material itself and of any results that
may be obtained from its use.

### Full Archives

The original code is archived under "pdst" in the Little Smalltalk archives:

https://github.com/kyle-github/littlesmalltalk/tree/master/archive

### Documentation

I'd recommend Timothy Budd's book "A Little Smalltalk", although it's quite dated now (as are most Smalltalk resources). Public Domain Smalltalk is essentially a clone of Little Smalltalk (the main difference being support for proper garbage collection).

## Fixes & Updates From Original

Inline syntax has been fixed (modern compilers take issue with functions which are marked `inline` but not marked `static`).

Support for underscores in names has been added with an optional ctype hack.

## Missing Parts

Only the virtual machine and standard library are included here. The tests, documentation and build scripts from the original (see link above) should still be relevant.

(This is coming from a larger private repository, where Smalltalk has been integrated into an operating system, so the original tests and build scripts didn't entirely make sense in this context.)

## Quick Start

TODO.
