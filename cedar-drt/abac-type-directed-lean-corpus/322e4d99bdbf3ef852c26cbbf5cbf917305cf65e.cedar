permit(
  principal == a::"",
  action == Action::"action",
  resource == a::"\0[\u{1c}"
) when {
  (true && (principal in ({"": 221866810263811, "\0\0\0[\u{1c}": false, "ks6\0\0\0\0\0": []}["ks6\0\0\0\0\0"]))) && false
};
