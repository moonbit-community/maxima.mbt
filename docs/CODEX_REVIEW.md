Found **15 actionable issues**, ranked below. Behavioral differences were checked with the existing release binary and `tools/maxima-ref`. No files were modified.

1. **P1 — Valid Unicode string operations can abort the process.**  
   [lisp/list.mbt:307](/Users/dii/git/maxima.mbt/lisp/list.mbt:307), [lisp/string.mbt:192](/Users/dii/git/maxima.mbt/lisp/string.mbt:192). `length` counts UTF-16 units, but character indexing counts code points.

   `?char("😀",?length("😀")-1);` aborts the port with exit **134**; the reference returns the character. Independently, `errcatch(?char("abc",3));` also aborts instead of catching an index error.

   **Fix:** use `string_length`, and raise Lisp conditions for invalid indices instead of allowing array panics.

2. **P1 — Mutating an `EQ`/`EQL` hash key makes its entry disappear.**  
   [lisp/hash.mbt:10](/Users/dii/git/maxima.mbt/lisp/hash.mbt:10). Identity-based tables nevertheless hash cons contents. Mutation changes the bucket used for lookup.

   ```maxima
   load(graphs)$
   block([a:[1],s],
     s:?new\-set(a),
     a[1]:2,
     ?set\-member(a,s));
   ```

   Port: **false**. Reference: **true**.

   **Fix:** give mutable identity keys stable identity hashes; reserve structural hashing for structural tests.

3. **P2 — Rational-to-double conversion rounds subnormals twice.**  
   [lisp/number.mbt:282](/Users/dii/git/maxima.mbt/lisp/number.mbt:282). Rounding the intermediate significand before `scalbn` loses information needed for final subnormal rounding.

   - `float((2^54+1)/2^1129);`: port **0.0**, reference **4.9406564584124654e-324**.
   - `float((3*2^54-1)/2^1129);`: port **9.881312916824931e-324**, reference **4.9406564584124654e-324**.

   **Fix:** round the exact rational once at the destination exponent, including subnormal precision.

4. **P2 — `RATIONALIZE` can return a rational representing the wrong float.**  
   [lisp/number.mbt:411](/Users/dii/git/maxima.mbt/lisp/number.mbt:411). The floating-point continued-fraction loop can overflow at `1.0 / frac`; after 64 iterations it returns an unchecked approximation.

   ```maxima
   ?coerce(?rationalize(1.0e-310),?double\-float);
   ```

   Port: **5.562684646268004e-309**. Reference: **9.99999999999997e-311**. Ordinary inputs also produce unnecessarily complicated fractions.

   **Fix:** search the exact rational rounding interval using integer arithmetic, and ensure the result rounds back to the input.

5. **P2 — Floating-point integer division turns overflow into a fabricated integer.**  
   [lisp/number.mbt:919](/Users/dii/git/maxima.mbt/lisp/number.mbt:919), [lisp/number.mbt:968](/Users/dii/git/maxima.mbt/lisp/number.mbt:968). `floor` and `truncate` bypass floating-point traps. Their infinity result reaches `integer_decode_float`, which treats it as finite.

   `?floor(1.0e308,1.0e-308);` and the corresponding `?truncate` return **2^1024** in the port; the reference signals floating-point overflow.

   **Fix:** check the division result before rounding/conversion, and reject nonfinite inputs in integer conversion helpers.

6. **P2 — Raising a CL ratio to zero violates numeric canonicalization.**  
   [lisp/number.mbt:1285](/Users/dii/git/maxima.mbt/lisp/number.mbt:1285). The ratio branch constructs `Ratio(1,1)` directly.

   `?integerp(?expt(?rational(0.5),0));` returns **false** instead of **true**; `eql` with integer `1` also fails.

   **Fix:** return integer `1` for exponent zero, or normalize through `make_ratio`.

7. **P2 — `EQUAL` equates strings with unrelated general vectors.**  
   [lisp/equality.mbt:66](/Users/dii/git/maxima.mbt/lisp/equality.mbt:66). Every string/vector comparison calls `lstring`; that conversion silently skips non-character elements.

   `?equal("",?vector(1,2));` returns **true** in the port and **false** in the reference.

   **Fix:** permit string comparison only with one-dimensional character arrays.

8. **P2 — Unicode classification rejects valid identifiers and accepts punctuation as letters.**  
   [lisp/string.mbt:102](/Users/dii/git/maxima.mbt/lisp/string.mbt:102), used by [core/nparse.mbt:69](/Users/dii/git/maxima.mbt/core/nparse.mbt:69). The block-range approximation omits Arabic and Devanagari.

   `عرب+عرب;` produces a parser error in the port; the reference returns **2*عرب**. With `stringproc` loaded, `[alphacharp("ع"),alphacharp("क"),alphacharp("・")]` gives **[false,false,true]**, versus **[true,true,false]**.

   **Fix:** use SBCL-compatible Unicode alphabetic classification.

9. **P2 — Generated keyword wrappers silently ignore unknown options.**  
   [tools/gen.py:524](/Users/dii/git/maxima.mbt/tools/gen.py:524), [core/glue.mbt:25](/Users/dii/git/maxima.mbt/core/glue.mbt:25). Wrappers extract recognized keys and allow unlimited arguments without validating the remainder.

   `run_testsuite(tests=[],nonsense=true);` returns **done**; the reference rejects `nonsense`. With LAPACK loaded, misspelling `alpha` as `alhpa` in `dgemm` silently computes using the default multiplier.

   **Fix:** generate complete keyword validation, preserving `&allow-other-keys` and distinguishing Maxima equations from CL keyword/value pairs.

10. **P2 — Keyword supplied-p flags are lost.**  
    [tools/analyze.py:93](/Users/dii/git/maxima.mbt/tools/analyze.py:93), [core/share_dgemm.mbt:20](/Users/dii/git/maxima.mbt/core/share_dgemm.mbt:20). The analyzer retains only keyword names/defaults. `dgemm` consequently infers suppliedness from the value.

    With LAPACK loaded, `dgemm(matrix([2.0]),matrix([3.0]),beta=0.0);` returns **matrix([6.0])**; the reference rejects supplying beta without C.

    **Fix:** preserve keyword supplied-p metadata and represent omission separately from an explicitly supplied default value.

11. **P2 — CL registrations discard arguments to `APPLY` and `MAPCAR`.**  
    [core/cl_functions.mbt:171](/Users/dii/git/maxima.mbt/core/cl_functions.mbt:171), [core/cl_functions.mbt:222](/Users/dii/git/maxima.mbt/core/cl_functions.mbt:222).

    With `simp:false$`:

    - `?apply(?max,100,?cdr([2,3]));` returns **3**, reference **100**.
    - `?car(?mapcar(?max,?cdr([1,2]),?cdr([3,4])));` returns **1**, reference **3**.

    **Fix:** prepend APPLY’s explicit arguments to its final list; MAPCAR must traverse all supplied lists together, stopping at the shortest.

12. **P2 — `DEFPARAMETER` incorrectly preserves existing values.**  
    [tools/gen.py:459](/Users/dii/git/maxima.mbt/tools/gen.py:459), also the quoted-initializer branch at line 457. Both generate `defvar_init`.

    Load `.repos/maxima/share/contrib/Grobner/grobner.lisp`, assign `?\*priority\-queue\-allocation\-size\*:99`, and reload it. The port retains **99**; the reference restores **16**.

    **Fix:** emit unconditional initialization for `defparameter`, using the variable kind already recorded by the analyzer.

13. **P2 — Runtime scientific formatting silently changes numeric output.**  
    [lisp/format.mbt:722](/Users/dii/git/maxima.mbt/lisp/format.mbt:722), [lisp/format.mbt:309](/Users/dii/git/maxima.mbt/lisp/format.mbt:309). Decimal digits are truncated, and `~G` uses the `~E` implementation.

    - `?format(false,"~,2E",1.999);`: **"1.99e+0"**, reference **"2.00e+0"**.
    - `?format(false,"~,2G",1.999);`: **"1.99e+0"**, reference **"2.0    "**.

    **Fix:** implement rounding with exponent carry and separate `~G` notation selection. `$printf` uses a separate implementation and is unaffected by these examples.

14. **P2 — Hash-table counting introduces quadratic workloads.**  
    [lisp/hash.mbt:169](/Users/dii/git/maxima.mbt/lisp/hash.mbt:169). Counting calls `entries()`, traversing entries and constructing another hash table, despite an already-maintained `count` field.

    Populate a graphs `?new\-set()` with N integers, then call `?set\-emptyp` N times. At N=2,000/4,000, the port took **2.4/8.6 seconds**; the reference took approximately **0.08 seconds** for either.

    **Fix:** return the maintained count directly.

15. **P2 — Character indexing makes TeX escaping quadratic.**  
    [lisp/string.mbt:193](/Users/dii/git/maxima.mbt/lisp/string.mbt:193), [core/mactex.mbt:134](/Users/dii/git/maxima.mbt/core/mactex.mbt:134). Every `char_at` constructs an array containing the entire string; `quote_chars` calls it for each character, replacing a linear Lisp scan.

    For `tex1` on ASCII strings of 10,000/20,000 characters, the port took **0.72/2.35 seconds**, versus **0.04/0.04 seconds** in the reference.

    **Fix:** iterate characters directly or construct the character array once per scan.

The central translation spot checks were encouraging: **107 algebra/evaluation cases and six display cases matched**, with no additional demonstrated translation bug. The main remaining risk is shared runtime and generated-contract behavior: these defects affect otherwise faithful translations and warrant targeted regression coverage beyond Maxima’s existing suites.