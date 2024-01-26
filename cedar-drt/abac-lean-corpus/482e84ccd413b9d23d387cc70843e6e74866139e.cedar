permit(
  principal == s::r::a::"\0",
  action in [s::r::Action::"action"],
  resource == s::r::a::"\0"
) when {
  true
};
