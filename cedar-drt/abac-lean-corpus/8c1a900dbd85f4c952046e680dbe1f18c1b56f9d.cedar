permit(
  principal,
  action,
  resource
) when {
  (true && ({"A": true in false}[""])) && ({"A": principal}[""])
};
