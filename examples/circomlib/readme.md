
### Information
Repository: https://github.com/iden3/circomlib.git
Commit: 0a045aec50d51396fcd86a568981a5a0afb99e95

### Change Log
 1. Adding import for `switcher.circom` and `smthash_poseidon.circom` to `smtprocessorlevel.circom` so that it compiles
 2. Adding import for `comparators.circom` to `smtlevins.circom` so that it compiles
 3. Adding import for `switcher.circom` and `smthash_poseidon.circom` to `smtverifierlevel.circom` so that it compiles
 4. Removed the main component in `sha256/main.circom` so that `main101.circom` could compile
 5. Added explicit invoke annotation to `SegmentMulFix` for component `cadders`
 6. Added explicit invoke annotation to `SegmentMulAny` for component `bits`
 7. Added explicit invoke annotation to `PoseidonEx` for component `mixS`
 8. Added explicit invoke annotation to `PoseidonEx` for component `sigmaF`
 9. Added explicit invoke annotation to `PoseidonEx` for component `ark`
 10. Added explicit invoke annotation to `EscalarMulAny` for component `adders`
 11. Added explicit invoke annotation to `EscalarMulFix` for component `adders`
 12. Added explicit invoke annotation to `SegmentMulFix` for component `adders`
 13. Added explicit invoke annotation to `EscalarMulFix` for component `segments`
 14. Added explicit invoke annotation to `EscalarMulAny` for component `segments`
 15. Added explicit invoke annotation to `SegmentMulFix` for component `windows`
 16. Added explicit invoke annotation to `SegmentMulFix` for component `dblLast`
 17. Added explicit invoke annotation to `PoseidonEx` for component `mix`
 18. Added explicit invoke annotation to `Sha256compression` for component `sume`
 19. Added explicit invoke annotation to `Sha256compression` for component `suma`
 20. Added explicit invoke annotation to `Sha256compression` for component `t1`
 21. Added explicit invoke annotation to `Sha256compression` for component `t2`
 22. Added explicit invoke annotation to `Sha256compression` for component `sigmaPlus`
 23. In template `BinSum` modified the size of output `out[nout]` so that it only referenced input variables
 24. Added explicit invoke annotation to `Sha256` for component `sha256compression`
 25. Added explicit invoke annotation to `Segment` for component `adders`
 26. Added explicit invoke annotation to `Segment` for component `windows`
 27. Added explicit invoke annotation to `Pedersen` for component `adders`
 28. Added explicit invoke annotation to `EscalarMul` for component `windows`
 29. Added explicit invoke annotation to `MiMCSponge` for component `S`
 30. Added explicit invoke annotation to `Multiplexer` for component `ep`
 31. Added explicit invoke annotation to `Pedersen` (in `pedersen_old.circom`) for component `escalarMuls`
 32. Added explicit invoke annotation to `PoseidonEx` for component `sigmaP`
 33. Added explicit invoke annotation to `Pedersen` for component `segments`
 34. Added explicit invoke annotation to `Sha256compression` for component `fsum`, `ct_k`

### Notes
 1. We were unable to compile the `Poseidon` circuit in `poseidon_old.circom` which is a known issue. We therefore did not include it in the benchmark set (corresponded to `main18.circom`).
 2. Recursive circuits are not supported so the recursive circuit `MultiAND` is excluded (`main59.circom`)
 3. Recursive circuits are not supported so `SMTProcessor` which invokes the recursive circuit `MultiAND` is excluded (`main92.circom`)
 4. Recursive circuits are not supported so `SMTVerifier` which invokes the recursive circuit `MultiAND` is excluded (`main88.circom`)
 5. The `LessThan` main component was duplicated because the main script created a duplicate for the commented out version of the template. Therefore `main23.circom` was removed