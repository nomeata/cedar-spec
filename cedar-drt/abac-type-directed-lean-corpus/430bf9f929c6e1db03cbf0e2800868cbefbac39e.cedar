permit(
  principal == a::"6\u{1}i",
  action == Action::"action",
  resource == a::"6\u{1}i"
) when {
  ((true && ([(ip("54.54.54.54")).isIpv4(), principal in principal].containsAll([]))) && (action has "N")) && (action has "")
};
