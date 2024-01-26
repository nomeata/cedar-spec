forbid(
  principal,
  action in [Action::""],
  resource == a::"\0Set\0\0"
) when {
  (false && Action::"") && context
};
