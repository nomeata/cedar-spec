permit(
  principal,
  action,
  resource == a::"6"
) when {
  ((true && ((if ((decimal("0.1")) == (decimal("0.1"))) then (decimal("##")) else (decimal("###"))) == (decimal("##")))) && ((action has "") == true)) && false
};
