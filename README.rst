
bmap
====

A high performance version of a B-Tree map.

Highlights:

- Fast iteration, especially for small maps (2-10x improvement over libstd's BTreeMap)

Future plans:

- Comparator support
- Parameterize over the max order statically, when generics
  or associated constants in rust permit it.


Documentation
-------------

API is still changing, depend on explicit 0.x versions to avoid breakage.

**Note: docs & crate are not available yet**

How to use with cargo::

    [dependencies]
    bmap = "0.1"

Please read the `API documentation here`__

__ http://bluss.github.io/bmap

|build_status|_ |crates|_

.. |build_status| image:: https://travis-ci.org/bluss/bmap.svg?branch=master
.. _build_status: https://travis-ci.org/bluss/bmap

.. |crates| image:: http://meritbadge.herokuapp.com/bmap
.. _crates: https://crates.io/crates/bmap

Recent Changes
--------------

- 0.1.1
