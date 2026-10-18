import Examples.HeaderCodec
import Examples.NestedLists
import Examples.Offer
import Examples.Router
import Examples.OriginRegex

/-! Run every example: `lake exe examples`. -/

def main : IO Unit := do
  IO.println "== Keel.Codec: a length-prefixed header list"
  Examples.HeaderCodec.run
  IO.println "== Keel.Parse: nested lists with fixDepth"
  Examples.NestedLists.run
  IO.println "== Keel.Refine: Offer, refined fields, located errors"
  Examples.Offer.run
  IO.println "== Keel.Route: a router, both Allow policies"
  Examples.Router.run
  IO.println "== Keel.Regex: an origin allow-list, fullmatch vs search"
  Examples.OriginRegex.run
