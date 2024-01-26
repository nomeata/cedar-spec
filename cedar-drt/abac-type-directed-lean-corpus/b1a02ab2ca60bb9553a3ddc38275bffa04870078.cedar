@F100("\0\0\0\0")
@r("\u{5}l")
forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  (true && (action has "")) && (action has "")
};
