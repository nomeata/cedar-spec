forbid(
  principal == a::"",
  action == Action::"action",
  resource
) when {
  true && ({"": false, "\u{1}\0\0~\0": (-9223372036854775808)}[""])
};
