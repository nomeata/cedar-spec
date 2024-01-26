permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::"\u{10} \0"
) when {
  true && (a::"" <= Action::"action")
};
