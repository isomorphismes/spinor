# MATH-LANG-B01 — Lifted axial rotations

The finite quaternion subgroup `Q₈ = {±1, ±i, ±j, ±k}` maps to the four diagonal rotations of a right-handed frame. It gives an exact test of the loss of information in Spinor's existing floating-point orientation projection. The motivating code is [Spinor's axial quaternion and rotation matrix](https://github.com/isomorphismes/spinor/blob/8052dbb49792603d5eb33d4b3f762d6d0ecc70ee/native/spinor_core.c#L69), with [its 0, 2π, 4π host assertions](https://github.com/isomorphismes/spinor/blob/8052dbb49792603d5eb33d4b3f762d6d0ecc70ee/native/test_spinor_core.c#L26). This experiment follows [the paired-mathematics job](https://github.com/isomorphisms/ai-ci/issues/244) and uses [the geometry-carrier distinctions](https://github.com/isomorphisms/Idric/issues/108).

## Type sketch

- `Lift` is a sign and a basis quaternion (`1`, `i`, `j`, or `k`). These eight elements each have norm one by their representation. `Orientation` has four alternatives representing the identity and the three coordinate half-turns. `Diagonal` describes their signs on the three spatial basis vectors.
- `antipode : Lift → Lift` flips the sign. `project : Lift → Orientation` forgets it via quaternion conjugation on pure quaternions. `multiply : Lift → Lift → Lift` uses the signed Hamilton table. Left multiplication acts after right multiplication. Equality of diagonal rotations is equality of their actions on the three basis vectors.
- For any `lift`, `project (antipode lift) = project lift`, while `antipode lift = lift` is impossible. Any pair with equal projection is equal or antipodal. Each orientation has a positive representative. Composition of quaternion lifts projects to composition of diagonal rotations.
- The exact axial half-turn checkpoints at `0, π, 2π, 3π, 4π` have lifts `1, k, −1, −k, 1`. The corresponding orientations are identity, z half-turn, identity, z half-turn, identity. Distinct visits to the same lift still need path data to differentiate them, as in the native model's unwrapped physical angle.
- The mathematics is pure. Typechecking requires no floating-point, FFI or Android runtime. The Idriç fixtures may execute under the compiler's owned Chez host lane for an additional runtime check.

## Convention and scope

The multiplication tables follow Hamilton's convention, with `ij = k`, `ji = −k`, and `i² = j² = k² = −1`. By conjugation, `i` and `−i` both preserve the `i` vector and negate the `j` and `k` vectors. Cycling the axes yields the other half-turns. The resulting diagonal matrices have determinant `+1` because they flip zero or two signs. See Jean Gallier, [*The Quaternions and the Spaces S³, SU(2), SO(3), and ℝP³*](https://www.cis.upenn.edu/~cis5150/gma-v2-chap9.pdf), §§9.1–9.2, for the identities and conjugation action. The source proves finite claims about the restricted map. The topology of the continuous covering, arbitrary rotated axes, the Hopf map to S², and the floating-point and Android implementations are outside this experiment.

## Evidence

The sources are `idric/LiftedRotations.idric` and `agda/LiftedRotations.agda`. `fixtures.tsv` records the shared cases. The Agda fixture module states these values as equalities. The Idriç fixture executable prints the corresponding rows in order.

Agda 2.6.3 checked `RotationFixtures.agda` from `agda/` using `--no-libraries --safe --without-K`. The proof verifies conjugation on every spatial basis vector for every lift. Changing `ij` to `−k` in a separate copy caused the same check to reject `conjugation-is-diagonal` at the `+i` lift acting on the y axis, with `plus != minus of type Sign`.

Idriç [2bce7677f513d711875e978bd6f5ad28b9e54d58](https://github.com/isomorphisms/Idric/commit/2bce7677f513d711875e978bd6f5ad28b9e54d58), built with Chez 10.4.1, checked both Idriç modules in `idric/` and compiled the fixture executable using `--cg chez --build rotation-fixtures.ipkg`. For a source checkout, use the built `_/build/exec/idris2` path, expose the checkout's `_/.tools/bin` on `PATH`, and set `IDRIS2_PATH` to the built prelude and base `build/ttc` directories. `IDRIS2_DATA` refers to `_/support`, and both `IDRIS2_LIBS` and `LD_LIBRARY_PATH` point to `_/support/c`.

Running `build/exec/rotation-fixtures` from `idric/` produced all seven rows byte-for-byte as in `fixtures.tsv` (`8be7a11f05a041838622b9424216e786b43ad8fce425b58e79ef12ab05f022a8`, SHA-256). In a separate copy with the sign of `ij` reversed, the compiler rejected `ordered_half_turns_differ` with a mismatch between `minus_sign` and `plus_sign`. The proof and execution evidence applies to this example's compiler pin and the host Chez target.
