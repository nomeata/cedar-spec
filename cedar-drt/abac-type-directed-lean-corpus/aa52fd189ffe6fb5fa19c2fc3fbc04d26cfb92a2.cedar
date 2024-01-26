permit(
  principal == a::"\0\0\0\0\0]\u{1}\0\0[\u{1c}",
  action == Action::"action",
  resource == a::""
) when {
  (true && (principal in ({"ks6\0\0\0\0\0\0:": []}["ks6\0\0\0\0\0\0:"]))) && false
};
