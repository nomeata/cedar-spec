forbid(
  principal == r::a::"",
  action in [r::Action::"action"],
  resource in r::a::"\0\0\0"
) when {
  true
};
