
bmap
====

A version of a B-Tree map based on ArrayVec

Highlights:

- Fast iteration, especially for small maps (up to 50% shorter runtime compared
  with libstd's BTreeMap in iteration microbenchmarks)

Future plans:

- Comparator support
- Parameterize over the max order statically, when generics
  or associated constants in rust permit it.


Documentation
-------------

API is still changing, depend on explicit 0.x versions to avoid breakage.

**Note: docs & crate are not published yet, sorry!**

|build_status|_ |crates|_

.. |build_status| image:: https://travis-ci.org/bluss/bmap.svg?branch=master
.. _build_status: https://travis-ci.org/bluss/bmap

.. |crates| image:: http://meritbadge.herokuapp.com/bmap
.. _crates: https://crates.io/crates/bmap

Recent Changes
--------------

- 0.1.1
