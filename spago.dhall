{ name = "dissect"
, dependencies =
  [ "bifunctors"
  , "console"
  , "effect"
  , "either"
  , "fixed-points"
  , "foreign-object"
  , "functors"
  , "lists"
  , "maybe"
  , "newtype"
  , "ordered-collections"
  , "partial"
  , "prelude"
  , "safe-coerce"
  , "st"
  , "tailrec"
  , "tuples"
  , "typelevel-prelude"
  , "unsafe-coerce"
  , "variant"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
, license = "BSD-3-Clause"
, repository = "https://github.com/PureFunctor/purescript-dissect.git"
}
