permit(
  principal,
  action in [r::r::Action::"action"],
  resource is r::r::a in r::r::a::""
) when {
  true && (r::r::a::"" has "")
};
