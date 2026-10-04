Two-size Gasoline: a tight guarantee for iterative rounding
=========================================================

For positive integer demands and delivery sizes 1 and K, position-first
iterative rounding satisfies::

    capacity <= initial fractional LP + K - 2 <= OPT + K - 2.

For each integer K >= 3, a family with 2K - 3 days attains OPT = K and
algorithm capacity 2K - 2 under original-index tie breaking. Thus the exact
worst-case ratio is 2 - 2/K. For K = 2 the algorithm is optimal.

This is a public research announcement, not a peer-reviewed publication.
VibeMathed currently lists the result as Candidate / Lean-checked. Its review
requested an explicit bridge from the LP-based algorithm to the score-based
formal run; the new bridge below addresses that request. The new bridge has
not yet received independent human review.

Interactive laboratory: https://mathiseveneasier.github.io/gasoline-two-sizes/site/

Repository: https://github.com/MathIsEvenEasier/gasoline-two-sizes

Inspect the work
----------------

* site/index.html: interactive laboratory; run a static web server at this
  directory and open /site/.
* research-notes.tex: mathematical proof and scope.
* formal/Result.lean: final witness statement and axiom audit targets.
* formal/Algorithm1.lean: complete equivalence of LP-based and score-based runs.
* formal/AssignmentLP.lean: assignment-LP feasibility and its attained minimum.
* algorithm-bridge.rst: correspondence with the source, tie rules and LP convention.
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

The 4 October Azure build compiled all eleven current Lean modules and
checked axiom dependencies for 24 targets, including the new LP bridge.
Lean rejected the deliberately false equality used as a negative control.
See evidence/algorithm-bridge-audit.json and its source hashes and logs.

The earlier Nanoda audit independently checked 9,451 declarations for the
original 12 targets. It does not cover the new bridge. The historical proof
export, checker configuration, logs and pinned tool revisions are retained.
All Azure resources used by the recorded jobs have been deleted; the cleanup
receipts are included.

Independent review of the new bridge is pending.
The Lean and Nanoda checks establish their respective formal propositions;
the finite Python and browser checks exercise the separate implementations.

Check the fixed examples
-----------------------

Run with Python 3, without external packages::

    python3 scripts/verify.py
    python3 scripts/verify_bridge_evidence.py

The first command exercises fixed implementation examples. The second checks
recorded evidence integrity and source hashes; it does not rerun Lean. The universal theorem is
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

AssignmentLP.lean independently defines the residual assignment LP using
matrix variables and actual inventory constraints. Algorithm1.lean proves
``run_iff_algorithm1`` and transfers the additive and ratio guarantees to
LP-based runs, including a factor-two theorem for the all-small case.
The source convention is explicit: Figure 1.1 prints sums <= 1, while the
text before Proposition 3.1.2 says doubly stochastic. We use sums equal to
one, the standard assignment interpretation; see algorithm-bridge.rst.

The normalized model has supplies 0 and h=K-1. Add one to each supply and
demand to recover the original instance. Normalization.lean proves the
corresponding equivalence of inventory-band feasibility; original
capacity is normalized capacity plus one.

Scope and provenance
--------------------

The target is Conjecture 3.1.1 in Lucas Lorieau's 2024 thesis,
https://perso.limos.fr/~lulorieau/docs/thesis/Master_Thesis.pdf#page=27 .
This work resolves the full positive-integer two-size conjecture stated
there, under the doubly stochastic assignment interpretation above. It does
not resolve the broader unrestricted one-dimensional or multidimensional
conjectures. The prior-art search found no verified earlier resolution of the
claim, but does not establish priority.

Prepared by MathIsEvenEasier with OpenAI Codex (GPT-6 Astra).
Research inspired by @xamualexander, Dr. Samuel Allen Alexander. Still there.
