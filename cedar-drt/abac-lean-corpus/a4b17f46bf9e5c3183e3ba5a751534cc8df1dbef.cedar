permit(
  principal is AfwN1::K::r::M in AfwN1::K::r::M::"\0\0\u{13}\0",
  action in [AfwN1::K::r::Action::"action"],
  resource
) when {
  ((true && (!action)) && principal) && action
};
