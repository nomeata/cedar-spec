permit(
  principal == c::a::"",
  action in [c::Action::"action"],
  resource
) when {
  ((true && (action has "")) && (action has "")) && (action has "")
};
