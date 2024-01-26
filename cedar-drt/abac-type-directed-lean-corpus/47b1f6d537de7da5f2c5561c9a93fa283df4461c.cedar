forbid(
  principal,
  action in [Action::""],
  resource == a::""
) when {
  (true && ((if (action in action) then action else action) in action)) && false
};
