permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && a::"") && (((a::"" == a::"") == (a::"" == a::"")) == ((a::"" == a::"") == (a::"" == a::"\0")))) && principal
};
