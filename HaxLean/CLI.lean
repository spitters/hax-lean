module

public import HaxLean.Json
public import HaxLean.Json.Adapter
public import HaxLean.Json.IdTable
public import HaxLean.Json.Chunked
public import HaxLean.HaxAdapter
public import HaxLean.PrettyPrint
public import HaxLean.Pipeline


@[expose] public section
open Hax
open Lean (Json ToJson FromJson toJson fromJson?)

/-- The verified RFC 8259 JSON parser.
    An export written by `cargo hax json --use-ids` is returned in its inline
    form (`Hax.resolveIds`). -/
def Json.parseVerified (s : String) : Except String Json :=
  Hax.resolveIds <$> Hax.Json.parseJsonString s

/-- The item array of a hax frontend export (`HaxAdapter.haxExportArray`: the `Legacy`
    items of a hax 0.4 export, the bare array of a hax 0.3 export), parsed by
    `Json.Chunked.chunkedParseResolved T`: every value whose text exceeds `T` bytes is
    parsed element by element with the verified parser, and `T = 0` is the whole-file
    parse `Json.parseVerified`; the value is the same for every `T`. -/
def parseHaxExportItems (s : String)
    (T : Nat := Hax.Json.Chunked.defaultChunkThreshold) : Except String Json :=
  Hax.Json.Chunked.chunkedParseResolved T s >>= HaxAdapter.haxExportArray

/-- The item array of a hax frontend export (`parseHaxExportItems`), with its
    items listed once each and every `Mod` sub-item list emptied
    (`HaxAdapter.flattenModItems`), and the structs, enums and unions that share
    a short name named apart (`HaxAdapter.qualifyAdtCollisions`). -/
def parseHaxExport (s : String)
    (T : Nat := Hax.Json.Chunked.defaultChunkThreshold) : Except String Json :=
  parseHaxExportItems s T >>= fun j =>
    HaxAdapter.qualifyAdtCollisions (HaxAdapter.flattenModItems j)

/-- Read input from file or stdin. -/
def readInput (path : Option String) : IO String := do
  match path with
  | none | some "-" => do
    let stdin ← IO.getStdin
    stdin.readToEnd
  | some p => IO.FS.readFile p

/-- Struct metadata read off an already-parsed hax JSON value.
    Returns list of (struct_name, [(field_name, type_tag)]). -/
def structMetaOfJson (json : Json) : StructMeta :=
  let structInfos := HaxAdapter.parseStructDefsFromJson json
  structInfos.map fun si =>
    (si.name, si.fields.map fun fi => (fi.name, fi.typeTag, fi.impType))

/-- Command-line options. -/
structure Options where
  /-- The emit mode; `haxpipeT` runs only with `certified` (`--emit-certified`). -/
  emitMode : String := ""
  inputFile : Option String := none
  haxFormat : Bool := false
  help : Bool := false
  name : String := "result"
  filterFns : Option (List String) := none  -- only include these functions
  /-- Emit even when a call through `&mut` is left outside the write-back
      rewrite, so that its effect does not reach the caller. Off by default:
      such an extraction misdescribes the source. -/
  allowDroppedWriteback : Bool := false
  /-- Emit, beside each verbatim `_impExpr` literal, its ANF-normalised form
      and the `haxToLowCT` lowering of that form. Off by default: the two extra
      definitions pull the CatCrypt `LowCT` closure into the generated file,
      which the security-provenance consumers do not need. -/
  emitLowCT : Bool := false
  /-- The hax frontend export holding the definitions of the traits the crate
      uses. When set, `--emit-certified --hax` emits each trait as a class,
      each trait `impl` as an instance, and each generic function with its
      type parameters and trait bounds as binders (`Hax.ClassEmit`). -/
  emitClasses : Option String := none
  /-- Emit the hax-lib contracts of the crate (`Hax.ContractEmit`): the
      `requires`/`ensures` clauses of each function with a contract statement,
      each `#[hax_lib::lemma]` as a statement, and, with `--emit-classes`, the
      pre- and postcondition fields of each trait method with the `Contract`
      class of refinement obligations. -/
  emitContracts : Bool := false
  /-- The crates whose trait methods are nominal. With `--emit-certified
      --hax`, a call of a method declared by a trait of one of these crates
      carries the head `krate::Trait::method` in the `ImpExpr` and `TExpr`
      literals, and the surface definitions and the `Deps` class read the bare
      method name. A trait method of any other crate outside `core`, `std`,
      `alloc` and `primeir_hax` whose name is a runtime builtin carries the
      qualified head whatever the list, and is the `Deps` field `Trait_method`
      (`HaxAdapter.qualifiesTraitCall`, `HaxAdapter.surfaceTraitHead`). -/
  nominalKrates : List String := []
  /-- With `--emit-certified --hax`: print, beside each `f_texpr` literal that the
      struct-to-tuple rewrite `tStructToTuple` changes, the literals `f_texprS` and
      `f_impExprS` of the rewrite, with the values of the premises of its refinement
      theorems (`Hax.structTupleBlock`). -/
  structTuples : Bool := false
  /-- With `--emit-certified --hax`: print the literal `<name>_depsHeads` of the
      `Deps` heads as the `ImpExpr` and `TExpr` literals print them
      (`Hax.literalDepsHeads`). -/
  traitHeads : Bool := false
  /-- With `--emit-certified --hax`: in the `ImpExpr` and `TExpr` literals, each call
      of a declassification (`.declassify()`, `.declassify_ref()`, the inherent method of
      a secret newtype) carries the head `declassify` with the value as its one
      argument (`Hax.tDeclassifyHeads`). -/
  keepDeclassify : Bool := false
  /-- With `--emit-certified --hax`: print each function that reaches an operation that
      panics in Rust, or calls such a function, in `RustM` with the guarded operations of
      `HaxLean.RuntimeM` (`Hax.MonadicEmit`); every other function is printed as without
      the flag. -/
  emitMonadic : Bool := false
  /-- With `--emit-certified --hax --emit-monadic`: the module name of the extraction; the
      run prints, in place of the extraction, its companion module with the theorems
      `f_reading` of the monadic functions (`Hax.ReadingEmit.readingFile`). -/
  emitReading : Option String := none
  /-- With `--emit-certified --hax`: a function the adapter refuses is reported on
      stderr with its name and construct and omitted, and so is every function that
      calls an omitted one; the rest of the crate is translated. Without the flag the
      first refusal aborts the run. -/
  keepGoing : Bool := false
  /-- `--json-chunk N`: values of the hax export whose text exceeds `N` bytes are parsed
      element by element (`parseHaxExportItems`); `none` is the default threshold. -/
  jsonChunk : Option Nat := none
  /-- The arguments starting with `--` that name no option, in order; `haxpipeT`
      stops with an error when there is one. -/
  unknownArgs : List String := []

/-- Parse command-line arguments. -/
def parseArgs (args : List String) : Options :=
  go args {}
where
  go : List String → Options → Options
    | [], opts => opts
    | "--emit-certified" :: rest, opts => go rest { opts with emitMode := "certified" }
    | "--hax" :: rest, opts => go rest { opts with haxFormat := true }
    | "--help" :: _, opts => { opts with help := true }
    | "--name" :: n :: rest, opts => go rest { opts with name := n }
    | "--filter" :: fns :: rest, opts =>
      go rest { opts with filterFns := some (fns.splitOn ",") }
    | "--allow-dropped-writeback" :: rest, opts =>
      go rest { opts with allowDroppedWriteback := true }
    | "--emit-lowct" :: rest, opts => go rest { opts with emitLowCT := true }
    | "--emit-classes" :: file :: rest, opts =>
      go rest { opts with emitClasses := some file }
    | "--emit-contracts" :: rest, opts => go rest { opts with emitContracts := true }
    | "--nominal-crates" :: ks :: rest, opts =>
      go rest { opts with nominalKrates := ks.splitOn "," |>.filter (!·.isEmpty) }
    | "--struct-tuples" :: rest, opts => go rest { opts with structTuples := true }
    | "--trait-heads" :: rest, opts => go rest { opts with traitHeads := true }
    | "--keep-declassify" :: rest, opts => go rest { opts with keepDeclassify := true }
    | "--emit-monadic" :: rest, opts => go rest { opts with emitMonadic := true }
    | "--emit-reading" :: m :: rest, opts => go rest { opts with emitReading := some m }
    | "--keep-going" :: rest, opts => go rest { opts with keepGoing := true }
    | "--json-chunk" :: n :: rest, opts =>
      match n.toNat? with
      | some k => go rest { opts with jsonChunk := some k }
      | none => go rest { opts with unknownArgs := opts.unknownArgs ++ ["--json-chunk " ++ n] }
    | arg :: rest, opts =>
      if arg.startsWith "--" then go rest { opts with unknownArgs := opts.unknownArgs ++ [arg] }
      else go rest { opts with inputFile := some arg }

/-- The text `haxpipeT --help` prints. -/
def helpText : String :=
"haxpipeT — Verified Hax Pipeline (Lean 4)

USAGE:
  haxpipeT --hax --emit-certified [OPTIONS] [INPUT_FILE]
  haxpipeT --python DUMP [--name NAME] [-o FILE]

OPTIONS:
  --hax             Input is a hax frontend export (cargo hax json)
  --emit-certified  Print the extraction module: the Lean definitions with
                    their ImpExpr and TExpr literals; required with --hax
  --name NAME       Name of the extraction (default: result)
  --filter FN,FN    Only include matching functions (comma-separated)
  --emit-lowct      With --emit-certified: also emit the ANF-normalised literal
                    and its haxToLowCT lowering per function
  --emit-classes FILE
                    With --emit-certified --hax: read the trait definitions
                    from the hax export FILE; emit each trait as a class, each
                    trait impl as an instance, and each generic function with
                    its type parameters and trait bounds as binders
  --emit-contracts  With --emit-certified --hax: emit the hax-lib contracts
                    (requires/ensures, lemmas; trait method pre- and
                    postconditions and their Contract class with
                    --emit-classes) as Prop definitions
  --nominal-crates CRATE,CRATE
                    With --emit-certified --hax: a call of a trait method of
                    one of these crates carries the head
                    CRATE::Trait::method in the ImpExpr and TExpr literals;
                    the surface definitions and the Deps class are unchanged.
                    A trait method of another crate named like a runtime
                    builtin (mul, eq, len, ...) carries the qualified head
                    without this option and is the Deps field Trait_method
  --struct-tuples   With --emit-certified --hax: beside each TExpr literal
                    that the struct-to-tuple rewrite changes, print the
                    literals f_texprS and f_impExprS of the rewrite and the
                    values of its two refinement premises
  --trait-heads     With --emit-certified --hax: print the literal
                    NAME_depsHeads, the Deps heads as the literals print them
  --keep-declassify With --emit-certified --hax: in the ImpExpr and TExpr
                    literals, each declassification call (.declassify(),
                    .declassify_ref(), the method of a secret newtype)
                    carries the head declassify with one argument
  --emit-monadic    With --emit-certified --hax: print each function that
                    reaches a panicking operation (checked arithmetic,
                    indexing, slicing, unwrap, assert), or calls such a
                    function, in RustM with the guarded operations of
                    HaxLean.RuntimeM; the other functions are unchanged
  --emit-reading MOD
                    With --emit-monadic: print, in place of the extraction
                    module MOD, its companion module with a theorem
                    f_reading per monadic function, relating it to the
                    toRustMSB reading of f_impExpr (imports MOD and
                    HaxAscent.RustSemantics.ReadingTac of catcrypt-compiler);
                    stderr gets one line reading-refused<TAB>f<TAB>construct
                    per function without a theorem, then a line
                    'reading: N emitted, M refused'
  --keep-going      With --emit-certified --hax: report each refused function
                    (REFUSED name: construct) and each function calling an
                    omitted one on stderr, omit them, and translate the rest
  --json-chunk N    Parse each value of the hax export whose text exceeds N
                    bytes element by element (default 4194304; 0 parses the
                    whole file at once); the parsed value is the same
  --python DUMP     Read the py2json dump of a module of the Python subset and
                    print its extraction module (with --name NAME, -o FILE);
                    a refusal is printed with its position and the run fails
  --help          Show this help message

INPUT:
  A hax frontend export (hax_frontend_export.json).
  Reads from stdin if no file specified (or \"-\").

NOTE (large inputs):
  The lexer runs in constant stack, so tokenizing a whole-crate export
  costs nothing in its length; the parser's array and object bodies are
  loops, and what recursion remains is over JSON nesting depth and over
  the AST, both small. `ulimit -s` governs none of this: Lean runs `main`
  on a thread whose stack it sizes itself.

EXAMPLES:
  haxpipeT --hax --emit-certified --name Crate hax_frontend_export.json
  haxpipeT --hax --emit-certified --filter f,g hax_frontend_export.json
"

