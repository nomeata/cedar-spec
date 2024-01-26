@A("\0")
@r("")
forbid(
  principal is r::r::r::r::r::r::r::r::A::r::a in r::r::r::r::r::r::r::r::A::r::a::"ij\0\0",
  action in [r::r::r::r::r::r::r::r::A::r::Action::"action"],
  resource
) when {
  (false && principal) && principal
};
