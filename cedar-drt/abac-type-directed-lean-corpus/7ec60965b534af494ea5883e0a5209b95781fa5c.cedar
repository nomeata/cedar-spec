permit(
  principal,
  action,
  resource == a::"6666666>6666"
) when {
  (true && (action has "")) && (action has "")
};
