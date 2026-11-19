import { domain, expect, law } from "@bytewaveco/pudding"
import { banner, framed, short } from "./banner.ts"

// True, but the strings are longer than Lean's kernel will compare.
law("a long banner reads the same however the marker was chosen", domain<boolean>(), wide => {
  expect(banner(wide)).toEqual(framed(wide))
})

law("FALSE: a long banner ignores which marker was asked for", domain<boolean>(), wide => {
  expect(banner(wide)).toEqual(framed(!wide))
})

law("a short banner is proved", domain<boolean>(), wide => {
  expect(short(wide)).toEqual(wide ? "=-<=-" : "=->=-")
})
