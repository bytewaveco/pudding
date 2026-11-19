import { domain, expect, law } from "@bytewaveco/pudding"
import { onHand, shelfValue } from "./stock.ts"

law("a pallet that comes in and goes straight out changes nothing",
  domain<[bigint, bigint, bigint]>(), ([received, shipped, pallet]) => {
    expect(onHand(received + pallet, shipped + pallet)).toEqual(onHand(received, shipped))
  })

law("what is on hand plus what was shipped is what was received",
  domain<[bigint, bigint]>(), ([received, shipped]) => {
    expect(onHand(received, shipped) + shipped).toEqual(received)
  })

law("counting two bins together or apart gives the same value",
  domain<[boolean, bigint, bigint]>(), ([writtenOff, first, second]) => {
    expect(shelfValue(first + second, writtenOff)).toEqual(shelfValue(first, writtenOff) + shelfValue(second, writtenOff))
  })

law("writing a bin off twice is not the same as keeping it", domain<bigint>(), units => {
  if (units !== 0n) expect(shelfValue(units, true)).not.toEqual(shelfValue(units, false))
})
