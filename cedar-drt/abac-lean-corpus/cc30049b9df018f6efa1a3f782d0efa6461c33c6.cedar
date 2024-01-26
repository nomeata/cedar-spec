forbid(
  principal == r::a::"\0\0\0",
  action in [r::Action::"action",r::Action::"action"],
  resource is r::a
) when {
  true && r::a::"\0\0\0"
};
