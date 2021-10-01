{ name = "dissect"
, dependencies =
  [ "bifunctors"
  , "either"
  , "functors"
  , "partial"
  , "prelude"
  , "tailrec"
  , "tuples"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
, license = "BSD-3-Clause"
, repository = "https://github.com/PureFunctor/purescript-dissect.git"
}
