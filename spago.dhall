{ name = "dissect"
, dependencies =
  [ "bifunctors"
  , "either"
  , "functors"
  , "partial"
  , "prelude"
  , "tailrec"
  , "tuples"
  , "typelevel-prelude"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "BSD-3-Clause"
, repository = "https://github.com/PureFunctor/purescript-dissect.git"
}
