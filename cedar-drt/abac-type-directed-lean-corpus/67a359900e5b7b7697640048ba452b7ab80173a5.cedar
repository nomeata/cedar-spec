forbid(
  principal,
  action in [x::Action::"action"],
  resource is x::a in x::a::""
) when {
  true
};
