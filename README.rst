Two-size Gasoline: a tight guarantee for iterative rounding
=========================================================

For positive integer demands and delivery sizes 1 and K, position-first
iterative rounding satisfies::

    capacity <= initial fractional LP + K - 2 <= OPT + K - 2.

For each integer K >= 3, a family with 2K - 3 days attains OPT = K and
algorithm capacity 2K - 2 under original-index tie breaking. Thus the exact
worst-case ratio is 2 - 2/K. For K = 2 the algorithm is optimal.

This is a public research announcement, not a peer-reviewed publication.
The formal statements have not yet received independent human review.

Interactive laboratory: https://mathiseveneasier.github.io/gasoline-two-sizes/site/

Repository: https://github.com/MathIsEvenEasier/gasoline-two-sizes

Inspect the work
----------------

* site/index.html: interactive laboratory; run a static web server at this
  directory and open /site/.
* research-notes.tex: mathematical proof and scope.
* formal/Result.lean: final witness statement and axiom audit targets.
* formal/Schedules.lean: comparison against any integral schedule.
* formal/Assignment.lean: equivalence of fractional assignment and the
  bounded fractional supply vector.
* scripts/fast_algorithm.py: exact decisions in O(n) arithmetic operations.
* scripts/oracle.py: independent exact cycle-path LP oracle.
* scripts/tightness_family.py: explicit extremal instances.
* prior-art.json: primary sources, search scope and limitations.
* evidence/: verification records and independent checker artifacts.
* recorded-audit/: the scripts used by the bounded Azure audit, retained
  for inspection; they require the recorded Azure supervisor environment.

Verification result
-------------------

The clean build passed all nine Lean modules. Nanoda independently checked
9,451 declarations for the 12 audited targets. Both checkers rejected
deliberately invalid controls. The proof export, checker configuration,
logs and pinned tool revisions are included. All Azure resources used by
the recorded jobs have been deleted; the cleanup receipts are included.

The theorem statements have not yet received independent human review.
The Lean and Nanoda checks establish the stated formal propositions;
the finite Python and browser checks exercise the separate implementations.

Check the fixed examples
-----------------------

Run with Python 3, without external packages::

    python3 scripts/verify.py

These finite checks exercise the implementations. The universal theorem is
proved in Lean, not inferred from the examples.

Rebuild the Lean proof
----------------------

Use an adequately resourced build environment. The recorded builds ran in
Azure with independent memory, runtime and resource deletion limits.
Lean 4.34.0 and mathlib commit 5ed2965256430c3649e86755f9576b54eca72435 are pinned::

    cd formal
    lake update
    lake exe cache get
    lake build
    lake env lean Result.lean

The axiom dependencies of the audited statements may only contain
propext, Classical.choice and Quot.sound. There are no admitted proofs,
custom axioms or native-decision proof shortcuts. Python and JavaScript
are separate implementations; their execution is not a premise of the
Lean theorems. The O(n) arithmetic complexity statement is a mathematical
and code analysis, not a formalized complexity theorem.

Formal model
------------

Reachability.lean models actual fractional deliveries and every peak and
trough, proves exact reachability and proves the prefix LP value is both a
lower bound and attained. IntegerModel.lean relates that real model to
integer scores. Rounding.lean defines all legal minimum-score runs, proves
their existence and bounds their actual trace ranges. Schedules.lean
defines unrestricted integral comparison schedules. Ties.lean realizes
any permitted tie path by an original input order. Sharpness.lean and
Result.lean give the matching family and an optimal integral comparison
schedule for every parameter.

The normalized model has supplies 0 and h=K-1. Add one to each supply and
demand to recover the original instance. Normalization.lean proves the
corresponding equivalence of inventory-band feasibility; original
capacity is normalized capacity plus one.

Scope and provenance
--------------------

The target is Conjecture 3.1.1 in Lucas Lorieau's 2024 thesis,
https://perso.limos.fr/~lulorieau/docs/thesis/Master_Thesis.pdf#page=27 .
This work concerns the positive-integer two-size subcase. It does not
resolve unrestricted one-dimensional supplies or the multidimensional
problem. The prior-art search found no verified earlier resolution of the
claim, but does not establish priority.

Prepared by MathIsEvenEasier with OpenAI Codex (GPT-6 Astra).
Research inspired by @xamualexander, Dr. Samuel Allen Alexander. Still there.
