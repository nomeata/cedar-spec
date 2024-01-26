forbid(
  principal == a::"\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12}\u{12},\u{12}.\u{12}>666\06",
  action in [Action::"action"],
  resource
) when {
  true
};
