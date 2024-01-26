forbid(
  principal in a::"\0\0\0\0\0\0\0",
  action == Action::"action",
  resource in a::"\0\0\0\0\0\0\0"
) when {
  (true && ((("" == "") == ("" == "")) == (("" == "") == ("" == "pik\u{1}")))) && action
};
