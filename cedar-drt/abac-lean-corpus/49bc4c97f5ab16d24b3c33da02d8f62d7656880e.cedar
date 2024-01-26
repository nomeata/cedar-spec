permit(
  principal == a::"",
  action in [Action::"action"],
  resource in a::""
) when {
  ((true && (a::"ccc" == ((a::"" in action) || [context, false]))) && principal) && principal
};
