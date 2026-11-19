/** Units on hand after goods came in and went out. */
export function onHand(received: bigint, shipped: bigint): bigint {
  return received - shipped
}

/** How a count changes the value of the shelf: a write-off counts against it. */
export function shelfValue(units: bigint, writtenOff: boolean): bigint {
  return writtenOff ? -units : units
}
