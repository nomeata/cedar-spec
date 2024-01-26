forbid(
  principal == r::a::"\0\0!\0",
  action in [r::Action::"action",r::Action::"action",r::Action::"action"],
  resource is r::a in r::a::"\0\0!\0"
) when {
  true
};
