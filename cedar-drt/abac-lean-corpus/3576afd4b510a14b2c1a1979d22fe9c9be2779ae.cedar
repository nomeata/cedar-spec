@A("j")
permit(
  principal,
  action in [r::r::s::r::K::r::Action::"action"],
  resource == r::r::s::r::K::r::a::""
) when {
  (true && Ah000::"") && principal
};
