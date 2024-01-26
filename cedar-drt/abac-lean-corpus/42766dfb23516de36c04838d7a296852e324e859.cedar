permit(
  principal == r::a::"",
  action in [r::Action::"action"],
  resource is r::a in r::a::""
) when {
  true
};
