forbid(
  principal is r::a,
  action in [r::Action::"action"],
  resource == r::a::"\0"
) when {
  true
};
