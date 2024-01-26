forbid(
  principal in a::"k\0\0\0\0\0\0",
  action == Action::"action",
  resource in a::"k\0\0\0\0\0\0"
) when {
  (true && ((("" == "") == ("" == "")) == (("" == "ik\u{1}\0\0(") == (!Action::"action")))) && true
};
