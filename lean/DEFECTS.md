# Defects found in the supplied arguments

## D1. Historical note states exact polynomial degree without a leading coefficient hypothesis

Source: handoff `notes/01_completion/proof.md`, §7.1, immediately after
`P_x(t)=sum_(j=1)^(2n) c_j t^(2n+1-j)`: “Its degree is 2n”.

Minimal failing implication: having n coefficient pairs does not imply
the coefficient c_1 is nonzero. The zero stream is a counterexample.
Even an actual valid block can have zero output: use one 16-byte block
with words (0,q-1), seed 16, and distinct OH words k_i=i. Its final
additive operands are (0,0), its tag is 16 XOR 16=0, and its primary
compressor is zero. The one-block polynomial is zero, not degree two.

Correction: the degree is **at most** 2n; equality requires a nonzero
leading reduced low coefficient. The consolidated paper already states
the correct bound in §3.1, p.6 and §7.1, p.18. Its identity-event treatment
explicitly allows vanishing leading coefficients (§3.3, p.7).

Effect: a wording error in a retained source note, with no loss in either
claimed bound. Root counting needs only the upper bound. The existing
ProvenHashes development likewise retains an upper-degree theorem and
counts polynomial identities separately. No requested statement is changed.
