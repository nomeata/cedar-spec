permit(
  principal is a in a::"",
  action == Action::"action",
  resource in a::""
) when {
  ((true && ("CCCCCCC" == "C\0\u{1}\t66")) && false) && false
};
