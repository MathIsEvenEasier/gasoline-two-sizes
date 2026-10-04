Connecting the LP algorithm to the formal guarantee
==================================================

The reviewer identified a precise gap in presentation: ``Run`` selected the
minimum closed-form score, while Lorieau's Algorithm 1 solves an assignment
LP for every candidate. The new bridge defines the LP independently and
proves that both rules have exactly the same possible runs on valid inputs.

The formal chain
----------------

1. Normalize the units. ``Gasoline.normalization`` in
   ``Normalization.lean`` preserves inventory
   feasibility when each delivery and demand is reduced by one. Original
   capacity is normalized capacity plus one for nonempty input.

2. Define the residual assignment LP independently. ``MatrixBand`` in
   ``AssignmentLP.lean`` uses nonnegative assignment matrices with row and
   column sums equal to one, actual inventory peaks and troughs, and fixed
   prefix bounds. ``LPValue`` means an attained minimum of beta minus alpha.
   Neither definition mentions ``score`` or ``value``.

3. Eliminate the matrix without changing the feasible delivery vectors.
   ``assignment_to_fraction`` and ``fraction_to_assignment`` give both
   directions, including empty delivery classes. ``assignment_delivery``
   identifies the original delivery as ``1 + h * large_fraction``.

4. Characterize feasible inventory bands. ``reach_iff`` solves the recursive
   peak/trough constraints and terminal conservation condition.
   ``matrixBand_iff_band`` connects that characterization to the assignment
   LP, preserving the exact remaining supply counts.

5. Identify the actual optimum. ``prefix_lower`` bounds every feasible
   completion from below; ``prefix_attained`` constructs one attaining the
   bound. ``matrixLP_value`` combines both with the matrix correspondence to
   give the LP minimum ``prefixValue + 1``. ``ValidPrefix.lp_value`` transports
   the result to integer data. A lower-bound formula alone would not suffice.

6. Preserve each candidate decision. ``small_choice_iff`` and
   ``large_choice_iff`` prove that comparing attained candidate LP minima
   is equivalent to comparing integer scores, including equality and the
   cases where one delivery class is exhausted.

7. Preserve the complete execution predicate. ``ValidPrefix.small`` and
   ``ValidPrefix.large`` maintain the conditions needed at the next step.
   ``run_iff_algorithm1`` then proves equivalence between ``Run`` and the
   independently defined LP-based ``Algorithm1Run`` by induction. All
   minimum tie choices are permitted, including first-index ties.

8. Apply the bound and sharpness results. ``algorithm1_additive_guarantee``
   and ``algorithm1_ratio_bound`` transfer the proved bounds directly to
   the LP rule. ``algorithm1_two_approximation`` includes the all-small case;
   ``algorithm1_exists`` supplies an actual run and an integral schedule of
   its stated capacity. ``sharp_lp_run`` in ``Result.lean`` transfers every
   parameter of the matching extremal family.

Coordinates and residual matrices
---------------------------------

The formal coordinates are ``h = K - 1`` and ``d_j = y_j - 1``. The counts
``m, k`` record remaining large and small deliveries. A valid prefix satisfies
``sum(ds) - s = h*m`` and contains the accumulated inventory extrema ``A, B``.
Original-unit capacity is normalized capacity plus one for a nonempty input.

Fixing a chosen matrix entry to one leaves all other entries in that row and
column zero. Deleting the fixed rows and columns leaves the residual assignment
matrix used by ``MatrixBand``; conversely append the fixed permutation block.
Their already fixed inventory constraints are exactly the prefix extrema.
Items of the same size give identical candidate LPs, so only two candidate
sizes need comparison. These identifications with the paper's notation remain
part of the mathematical model review; Lean checks the definitions stated here.

Ties
----

``Algorithm1Run`` allows every minimum-LP choice. Algorithm 1's fixed scan
order chooses one of these minima, so its guarantee follows regardless of
that order. Equivalence does not assert that every allowed tie path occurs
for one particular preselected input order. ``run_realizable`` separately
proves that any allowed score path can be realized by an original input order,
and ``exact_ratio_witness`` includes the first-index extremal construction.

Source convention requiring explicit attention
----------------------------------------------

The source is Lucas Lorieau's 2024 thesis:
https://perso.limos.fr/~lulorieau/docs/thesis/Master_Thesis.pdf .
Algorithm 1 is on printed page 8; Conjecture 3.1.1 is on printed page 21.
The whole conjecture is the positive-integer two-size case treated here.
The unrestricted one-dimensional conjecture is a broader question.

Figure 1.1 on printed page 4 displays row and column bounds with ``<= 1``.
The discussion before the proof of Proposition 3.1.2 on printed page 16
explicitly describes the relaxation as doubly stochastic. We formalize that
standard assignment interpretation, with sums equal to one and all supplies
used. We do not claim equivalence with the literal weaker inequalities in
Figure 1.1. This discrepancy should be visible to anyone reviewing the
translation from the source to the formal model.

For a concrete distinction, take supplies (1,3), demands (2,2), and fix the
first delivery to 1. The equality model must then use all 3 units of the
remaining item, requiring capacity 3. Replacing the row and column equalities
by inequalities, without a total-use condition, permits the residual matrix
entry 2/3 and delivers only 2 units. Starting with stock 1, the inventory
trace becomes (1,2,0,2,0), of range 2, instead of (1,2,0,3,1), of range 3.
The weaker model omits one unit of supply. This shows why the stated
convention matters; it is not a claim about every other index printed in
Figure 1.1 or about a model with an additional total-use constraint.

Verification scope
------------------

See ``evidence/algorithm-bridge-audit.json`` for the new Azure build, exact
source hashes, theorem axiom lists and the rejected negative control.
The original Nanoda record covers its original 12 targets only. The new
bridge is checked by Lean and is not included in that historical Nanoda export.
No independent human audit of the new bridge is claimed.

Prepared by MathIsEvenEasier with OpenAI Codex (GPT-6 Astra).
