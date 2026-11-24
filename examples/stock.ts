export function onHand(received: bigint, shipped: bigint): bigint {
  return received - shipped
}

export function shelfValue(units: bigint, writtenOff: boolean): bigint {
  return writtenOff ? -units : units
}
